%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT2034+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:03 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
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
                     => ? [X4] :
                          ( r2_hidden(X2,k10_yellow_6(X0,X4))
                          & m2_yellow_6(X4,X0,X3) ) )
                  & ~ r2_hidden(X2,k10_yellow_6(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(X2,k10_yellow_6(X0,X4))
              | ~ m2_yellow_6(X4,X0,X3) )
          & m2_yellow_6(X3,X0,X1) )
     => ( ! [X4] :
            ( ~ r2_hidden(X2,k10_yellow_6(X0,X4))
            | ~ m2_yellow_6(X4,X0,sK2(X0,X1,X2)) )
        & m2_yellow_6(sK2(X0,X1,X2),X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ! [X4] :
                    ( ~ r2_hidden(X2,k10_yellow_6(X0,X4))
                    | ~ m2_yellow_6(X4,X0,sK2(X0,X1,X2)) )
                & m2_yellow_6(sK2(X0,X1,X2),X0,X1) )
              | r2_hidden(X2,k10_yellow_6(X0,X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f27])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m2_yellow_6(sK2(X0,X1,X2),X0,X1)
      | r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

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

fof(f3,axiom,(
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

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r3_waybel_9(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X1,sK0(X0,X1))
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r3_waybel_9(X0,X1,sK0(X0,X1))
            & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f23])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK0(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f49,plain,(
    v1_compts_1(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f48,plain,(
    v8_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r3_waybel_9(X0,X1,sK0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
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

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f41,plain,(
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
    inference(cnf_transformation,[],[f16])).

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
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( ! [X3] :
                      ( m2_yellow_6(X3,X0,X1)
                     => ~ r2_hidden(X2,k10_yellow_6(X0,X3)) )
                  & r3_waybel_9(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,k10_yellow_6(X0,X3))
          & m2_yellow_6(X3,X0,X1) )
     => ( r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2)))
        & m2_yellow_6(sK1(X0,X1,X2),X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f25])).

fof(f43,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f42,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X2,k10_yellow_6(X0,X4))
      | ~ m2_yellow_6(X4,X0,sK2(X0,X1,X2))
      | r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_11,plain,
    ( m2_yellow_6(sK2(X0,X1,X2),X0,X1)
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_471,plain,
    ( m2_yellow_6(sK2(X0,X1,X2),X0,X1)
    | r2_hidden(X2,k10_yellow_6(X0,X1))
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
    ( m2_yellow_6(sK2(sK3,X0,X1),sK3,X0)
    | r2_hidden(X1,k10_yellow_6(sK3,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l1_waybel_0(X0,sK3)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_471])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_476,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | m2_yellow_6(sK2(sK3,X0,X1),sK3,X0)
    | r2_hidden(X1,k10_yellow_6(sK3,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l1_waybel_0(X0,sK3)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_472,c_24,c_20])).

cnf(c_477,plain,
    ( m2_yellow_6(sK2(sK3,X0,X1),sK3,X0)
    | r2_hidden(X1,k10_yellow_6(sK3,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l1_waybel_0(X0,sK3)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_476])).

cnf(c_1826,plain,
    ( m2_yellow_6(sK2(sK3,X0_49,X0_50),sK3,X0_49)
    | r2_hidden(X0_50,k10_yellow_6(sK3,X0_49))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK3))
    | ~ l1_waybel_0(X0_49,sK3)
    | v2_struct_0(X0_49)
    | ~ v4_orders_2(X0_49)
    | ~ v7_waybel_0(X0_49) ),
    inference(subtyping,[status(esa)],[c_477])).

cnf(c_2276,plain,
    ( m2_yellow_6(sK2(sK3,X0_49,X0_50),sK3,X0_49) = iProver_top
    | r2_hidden(X0_50,k10_yellow_6(sK3,X0_49)) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | l1_waybel_0(X0_49,sK3) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v4_orders_2(X0_49) != iProver_top
    | v7_waybel_0(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1826])).

cnf(c_6,plain,
    ( m1_subset_1(sK0(X0,X1),u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_21,negated_conjecture,
    ( v1_compts_1(sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_257,plain,
    ( m1_subset_1(sK0(X0,X1),u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_21])).

cnf(c_258,plain,
    ( m1_subset_1(sK0(sK3,X0),u1_struct_0(sK3))
    | ~ l1_waybel_0(X0,sK3)
    | ~ v2_pre_topc(sK3)
    | ~ v8_pre_topc(sK3)
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
    | m1_subset_1(sK0(sK3,X0),u1_struct_0(sK3))
    | ~ l1_waybel_0(X0,sK3)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_258,c_24,c_23,c_22,c_20])).

cnf(c_263,plain,
    ( m1_subset_1(sK0(sK3,X0),u1_struct_0(sK3))
    | ~ l1_waybel_0(X0,sK3)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_262])).

cnf(c_1828,plain,
    ( m1_subset_1(sK0(sK3,X0_49),u1_struct_0(sK3))
    | ~ l1_waybel_0(X0_49,sK3)
    | v2_struct_0(X0_49)
    | ~ v4_orders_2(X0_49)
    | ~ v7_waybel_0(X0_49) ),
    inference(subtyping,[status(esa)],[c_263])).

cnf(c_2274,plain,
    ( m1_subset_1(sK0(sK3,X0_49),u1_struct_0(sK3)) = iProver_top
    | l1_waybel_0(X0_49,sK3) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v4_orders_2(X0_49) != iProver_top
    | v7_waybel_0(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1828])).

cnf(c_5,plain,
    ( r3_waybel_9(X0,X1,sK0(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_284,plain,
    ( r3_waybel_9(X0,X1,sK0(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_21])).

cnf(c_285,plain,
    ( r3_waybel_9(sK3,X0,sK0(sK3,X0))
    | ~ l1_waybel_0(X0,sK3)
    | ~ v2_pre_topc(sK3)
    | ~ v8_pre_topc(sK3)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_284])).

cnf(c_289,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | r3_waybel_9(sK3,X0,sK0(sK3,X0))
    | ~ l1_waybel_0(X0,sK3)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_285,c_24,c_23,c_22,c_20])).

cnf(c_290,plain,
    ( r3_waybel_9(sK3,X0,sK0(sK3,X0))
    | ~ l1_waybel_0(X0,sK3)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_289])).

cnf(c_1827,plain,
    ( r3_waybel_9(sK3,X0_49,sK0(sK3,X0_49))
    | ~ l1_waybel_0(X0_49,sK3)
    | v2_struct_0(X0_49)
    | ~ v4_orders_2(X0_49)
    | ~ v7_waybel_0(X0_49) ),
    inference(subtyping,[status(esa)],[c_290])).

cnf(c_2275,plain,
    ( r3_waybel_9(sK3,X0_49,sK0(sK3,X0_49)) = iProver_top
    | l1_waybel_0(X0_49,sK3) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v4_orders_2(X0_49) != iProver_top
    | v7_waybel_0(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1827])).

cnf(c_7,plain,
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
    inference(cnf_transformation,[],[f41])).

cnf(c_570,plain,
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
    inference(resolution_lifted,[status(thm)],[c_7,c_23])).

cnf(c_571,plain,
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
    inference(unflattening,[status(thm)],[c_570])).

cnf(c_573,plain,
    ( ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ r3_waybel_9(sK3,X0,X1)
    | r3_waybel_9(sK3,X2,X1)
    | ~ m2_yellow_6(X0,sK3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l1_waybel_0(X2,sK3)
    | v2_struct_0(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_571,c_24,c_20])).

cnf(c_574,plain,
    ( ~ r3_waybel_9(sK3,X0,X1)
    | r3_waybel_9(sK3,X2,X1)
    | ~ m2_yellow_6(X0,sK3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l1_waybel_0(X2,sK3)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2) ),
    inference(renaming,[status(thm)],[c_573])).

cnf(c_1823,plain,
    ( ~ r3_waybel_9(sK3,X0_49,X0_50)
    | r3_waybel_9(sK3,X1_49,X0_50)
    | ~ m2_yellow_6(X0_49,sK3,X1_49)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK3))
    | ~ l1_waybel_0(X1_49,sK3)
    | v2_struct_0(X1_49)
    | ~ v4_orders_2(X1_49)
    | ~ v7_waybel_0(X1_49) ),
    inference(subtyping,[status(esa)],[c_574])).

cnf(c_2279,plain,
    ( r3_waybel_9(sK3,X0_49,X0_50) != iProver_top
    | r3_waybel_9(sK3,X1_49,X0_50) = iProver_top
    | m2_yellow_6(X0_49,sK3,X1_49) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | l1_waybel_0(X1_49,sK3) != iProver_top
    | v2_struct_0(X1_49) = iProver_top
    | v4_orders_2(X1_49) != iProver_top
    | v7_waybel_0(X1_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1823])).

cnf(c_3229,plain,
    ( r3_waybel_9(sK3,X0_49,sK0(sK3,X1_49)) != iProver_top
    | r3_waybel_9(sK3,X2_49,sK0(sK3,X1_49)) = iProver_top
    | m2_yellow_6(X0_49,sK3,X2_49) != iProver_top
    | l1_waybel_0(X1_49,sK3) != iProver_top
    | l1_waybel_0(X2_49,sK3) != iProver_top
    | v2_struct_0(X1_49) = iProver_top
    | v2_struct_0(X2_49) = iProver_top
    | v4_orders_2(X2_49) != iProver_top
    | v4_orders_2(X1_49) != iProver_top
    | v7_waybel_0(X2_49) != iProver_top
    | v7_waybel_0(X1_49) != iProver_top ),
    inference(superposition,[status(thm)],[c_2274,c_2279])).

cnf(c_3990,plain,
    ( r3_waybel_9(sK3,X0_49,sK0(sK3,X1_49)) = iProver_top
    | m2_yellow_6(X1_49,sK3,X0_49) != iProver_top
    | l1_waybel_0(X1_49,sK3) != iProver_top
    | l1_waybel_0(X0_49,sK3) != iProver_top
    | v2_struct_0(X1_49) = iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v4_orders_2(X0_49) != iProver_top
    | v4_orders_2(X1_49) != iProver_top
    | v7_waybel_0(X0_49) != iProver_top
    | v7_waybel_0(X1_49) != iProver_top ),
    inference(superposition,[status(thm)],[c_2275,c_3229])).

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

cnf(c_1820,plain,
    ( ~ m2_yellow_6(X0_49,sK3,X1_49)
    | ~ l1_waybel_0(X1_49,sK3)
    | v2_struct_0(X1_49)
    | ~ v4_orders_2(X1_49)
    | ~ v7_waybel_0(X1_49)
    | v7_waybel_0(X0_49) ),
    inference(subtyping,[status(esa)],[c_706])).

cnf(c_2282,plain,
    ( m2_yellow_6(X0_49,sK3,X1_49) != iProver_top
    | l1_waybel_0(X1_49,sK3) != iProver_top
    | v2_struct_0(X1_49) = iProver_top
    | v4_orders_2(X1_49) != iProver_top
    | v7_waybel_0(X1_49) != iProver_top
    | v7_waybel_0(X0_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1820])).

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

cnf(c_1819,plain,
    ( ~ m2_yellow_6(X0_49,sK3,X1_49)
    | ~ l1_waybel_0(X1_49,sK3)
    | v2_struct_0(X1_49)
    | ~ v4_orders_2(X1_49)
    | v4_orders_2(X0_49)
    | ~ v7_waybel_0(X1_49) ),
    inference(subtyping,[status(esa)],[c_732])).

cnf(c_2283,plain,
    ( m2_yellow_6(X0_49,sK3,X1_49) != iProver_top
    | l1_waybel_0(X1_49,sK3) != iProver_top
    | v2_struct_0(X1_49) = iProver_top
    | v4_orders_2(X1_49) != iProver_top
    | v4_orders_2(X0_49) = iProver_top
    | v7_waybel_0(X1_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1819])).

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

cnf(c_1818,plain,
    ( ~ m2_yellow_6(X0_49,sK3,X1_49)
    | ~ l1_waybel_0(X1_49,sK3)
    | ~ v2_struct_0(X0_49)
    | v2_struct_0(X1_49)
    | ~ v4_orders_2(X1_49)
    | ~ v7_waybel_0(X1_49) ),
    inference(subtyping,[status(esa)],[c_758])).

cnf(c_2284,plain,
    ( m2_yellow_6(X0_49,sK3,X1_49) != iProver_top
    | l1_waybel_0(X1_49,sK3) != iProver_top
    | v2_struct_0(X0_49) != iProver_top
    | v2_struct_0(X1_49) = iProver_top
    | v4_orders_2(X1_49) != iProver_top
    | v7_waybel_0(X1_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1818])).

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

cnf(c_1821,plain,
    ( ~ m2_yellow_6(X0_49,sK3,X1_49)
    | ~ l1_waybel_0(X1_49,sK3)
    | l1_waybel_0(X0_49,sK3)
    | v2_struct_0(X1_49)
    | ~ v4_orders_2(X1_49)
    | ~ v7_waybel_0(X1_49) ),
    inference(subtyping,[status(esa)],[c_680])).

cnf(c_2281,plain,
    ( m2_yellow_6(X0_49,sK3,X1_49) != iProver_top
    | l1_waybel_0(X1_49,sK3) != iProver_top
    | l1_waybel_0(X0_49,sK3) = iProver_top
    | v2_struct_0(X1_49) = iProver_top
    | v4_orders_2(X1_49) != iProver_top
    | v7_waybel_0(X1_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1821])).

cnf(c_4038,plain,
    ( r3_waybel_9(sK3,X0_49,sK0(sK3,X1_49)) = iProver_top
    | m2_yellow_6(X1_49,sK3,X0_49) != iProver_top
    | l1_waybel_0(X0_49,sK3) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v4_orders_2(X0_49) != iProver_top
    | v7_waybel_0(X0_49) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3990,c_2282,c_2283,c_2284,c_2281])).

cnf(c_13,negated_conjecture,
    ( r3_waybel_9(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1836,negated_conjecture,
    ( r3_waybel_9(sK3,sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2266,plain,
    ( r3_waybel_9(sK3,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1836])).

cnf(c_15,negated_conjecture,
    ( ~ r3_waybel_9(sK3,sK4,X0)
    | ~ r3_waybel_9(sK3,sK4,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1834,negated_conjecture,
    ( ~ r3_waybel_9(sK3,sK4,X0_50)
    | ~ r3_waybel_9(sK3,sK4,X1_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK3))
    | X1_50 = X0_50 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2268,plain,
    ( X0_50 = X1_50
    | r3_waybel_9(sK3,sK4,X0_50) != iProver_top
    | r3_waybel_9(sK3,sK4,X1_50) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1834])).

cnf(c_2653,plain,
    ( sK5 = X0_50
    | r3_waybel_9(sK3,sK4,X0_50) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2266,c_2268])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_37,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2656,plain,
    ( m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | r3_waybel_9(sK3,sK4,X0_50) != iProver_top
    | sK5 = X0_50 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2653,c_37])).

cnf(c_2657,plain,
    ( sK5 = X0_50
    | r3_waybel_9(sK3,sK4,X0_50) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2656])).

cnf(c_4041,plain,
    ( sK0(sK3,X0_49) = sK5
    | m2_yellow_6(X0_49,sK3,sK4) != iProver_top
    | m1_subset_1(sK0(sK3,X0_49),u1_struct_0(sK3)) != iProver_top
    | l1_waybel_0(sK4,sK3) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK4) != iProver_top
    | v7_waybel_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4038,c_2657])).

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
    ( sK0(sK3,X0_49) = sK5
    | m2_yellow_6(X0_49,sK3,sK4) != iProver_top
    | m1_subset_1(sK0(sK3,X0_49),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4041,c_30,c_31,c_32,c_33])).

cnf(c_4300,plain,
    ( sK0(sK3,X0_49) = sK5
    | m2_yellow_6(X0_49,sK3,sK4) != iProver_top
    | l1_waybel_0(X0_49,sK3) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v4_orders_2(X0_49) != iProver_top
    | v7_waybel_0(X0_49) != iProver_top ),
    inference(superposition,[status(thm)],[c_2274,c_4291])).

cnf(c_2511,plain,
    ( ~ m2_yellow_6(X0_49,sK3,sK4)
    | ~ l1_waybel_0(sK4,sK3)
    | v2_struct_0(sK4)
    | v4_orders_2(X0_49)
    | ~ v4_orders_2(sK4)
    | ~ v7_waybel_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1819])).

cnf(c_2512,plain,
    ( m2_yellow_6(X0_49,sK3,sK4) != iProver_top
    | l1_waybel_0(sK4,sK3) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(X0_49) = iProver_top
    | v4_orders_2(sK4) != iProver_top
    | v7_waybel_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2511])).

cnf(c_2516,plain,
    ( ~ m2_yellow_6(X0_49,sK3,sK4)
    | ~ l1_waybel_0(sK4,sK3)
    | v2_struct_0(sK4)
    | ~ v4_orders_2(sK4)
    | v7_waybel_0(X0_49)
    | ~ v7_waybel_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1820])).

cnf(c_2517,plain,
    ( m2_yellow_6(X0_49,sK3,sK4) != iProver_top
    | l1_waybel_0(sK4,sK3) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK4) != iProver_top
    | v7_waybel_0(X0_49) = iProver_top
    | v7_waybel_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2516])).

cnf(c_2521,plain,
    ( ~ m2_yellow_6(X0_49,sK3,sK4)
    | l1_waybel_0(X0_49,sK3)
    | ~ l1_waybel_0(sK4,sK3)
    | v2_struct_0(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v7_waybel_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1821])).

cnf(c_2522,plain,
    ( m2_yellow_6(X0_49,sK3,sK4) != iProver_top
    | l1_waybel_0(X0_49,sK3) = iProver_top
    | l1_waybel_0(sK4,sK3) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK4) != iProver_top
    | v7_waybel_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2521])).

cnf(c_4318,plain,
    ( m2_yellow_6(X0_49,sK3,sK4) != iProver_top
    | sK0(sK3,X0_49) = sK5
    | v2_struct_0(X0_49) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4300,c_30,c_31,c_32,c_33,c_2512,c_2517,c_2522])).

cnf(c_4319,plain,
    ( sK0(sK3,X0_49) = sK5
    | m2_yellow_6(X0_49,sK3,sK4) != iProver_top
    | v2_struct_0(X0_49) = iProver_top ),
    inference(renaming,[status(thm)],[c_4318])).

cnf(c_4328,plain,
    ( sK0(sK3,sK2(sK3,sK4,X0_50)) = sK5
    | r2_hidden(X0_50,k10_yellow_6(sK3,sK4)) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | l1_waybel_0(sK4,sK3) != iProver_top
    | v2_struct_0(sK2(sK3,sK4,X0_50)) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK4) != iProver_top
    | v7_waybel_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2276,c_4319])).

cnf(c_2536,plain,
    ( m2_yellow_6(sK2(sK3,sK4,X0_50),sK3,sK4)
    | r2_hidden(X0_50,k10_yellow_6(sK3,sK4))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK3))
    | ~ l1_waybel_0(sK4,sK3)
    | v2_struct_0(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v7_waybel_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1826])).

cnf(c_2537,plain,
    ( m2_yellow_6(sK2(sK3,sK4,X0_50),sK3,sK4) = iProver_top
    | r2_hidden(X0_50,k10_yellow_6(sK3,sK4)) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | l1_waybel_0(sK4,sK3) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK4) != iProver_top
    | v7_waybel_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2536])).

cnf(c_3011,plain,
    ( ~ m2_yellow_6(sK2(sK3,sK4,X0_50),sK3,X0_49)
    | ~ l1_waybel_0(X0_49,sK3)
    | v2_struct_0(X0_49)
    | ~ v2_struct_0(sK2(sK3,sK4,X0_50))
    | ~ v4_orders_2(X0_49)
    | ~ v7_waybel_0(X0_49) ),
    inference(instantiation,[status(thm)],[c_1818])).

cnf(c_3533,plain,
    ( ~ m2_yellow_6(sK2(sK3,sK4,X0_50),sK3,sK4)
    | ~ l1_waybel_0(sK4,sK3)
    | ~ v2_struct_0(sK2(sK3,sK4,X0_50))
    | v2_struct_0(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v7_waybel_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3011])).

cnf(c_3534,plain,
    ( m2_yellow_6(sK2(sK3,sK4,X0_50),sK3,sK4) != iProver_top
    | l1_waybel_0(sK4,sK3) != iProver_top
    | v2_struct_0(sK2(sK3,sK4,X0_50)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK4) != iProver_top
    | v7_waybel_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3533])).

cnf(c_4937,plain,
    ( m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0_50,k10_yellow_6(sK3,sK4)) = iProver_top
    | sK0(sK3,sK2(sK3,sK4,X0_50)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4328,c_30,c_31,c_32,c_33,c_2537,c_3534])).

cnf(c_4938,plain,
    ( sK0(sK3,sK2(sK3,sK4,X0_50)) = sK5
    | r2_hidden(X0_50,k10_yellow_6(sK3,sK4)) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4937])).

cnf(c_12,negated_conjecture,
    ( ~ r2_hidden(sK5,k10_yellow_6(sK3,sK4)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1837,negated_conjecture,
    ( ~ r2_hidden(sK5,k10_yellow_6(sK3,sK4)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_2265,plain,
    ( r2_hidden(sK5,k10_yellow_6(sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1837])).

cnf(c_4946,plain,
    ( sK0(sK3,sK2(sK3,sK4,sK5)) = sK5
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4938,c_2265])).

cnf(c_39,plain,
    ( r2_hidden(sK5,k10_yellow_6(sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2539,plain,
    ( m2_yellow_6(sK2(sK3,sK4,sK5),sK3,sK4) = iProver_top
    | r2_hidden(sK5,k10_yellow_6(sK3,sK4)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | l1_waybel_0(sK4,sK3) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK4) != iProver_top
    | v7_waybel_0(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2537])).

cnf(c_3536,plain,
    ( m2_yellow_6(sK2(sK3,sK4,sK5),sK3,sK4) != iProver_top
    | l1_waybel_0(sK4,sK3) != iProver_top
    | v2_struct_0(sK2(sK3,sK4,sK5)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK4) != iProver_top
    | v7_waybel_0(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3534])).

cnf(c_4365,plain,
    ( sK0(sK3,sK2(sK3,sK4,sK5)) = sK5
    | r2_hidden(sK5,k10_yellow_6(sK3,sK4)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | l1_waybel_0(sK4,sK3) != iProver_top
    | v2_struct_0(sK2(sK3,sK4,sK5)) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK4) != iProver_top
    | v7_waybel_0(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4328])).

cnf(c_4949,plain,
    ( sK0(sK3,sK2(sK3,sK4,sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4946,c_30,c_31,c_32,c_33,c_37,c_39,c_2539,c_3536,c_4365])).

cnf(c_4954,plain,
    ( r3_waybel_9(sK3,sK2(sK3,sK4,sK5),sK5) = iProver_top
    | l1_waybel_0(sK2(sK3,sK4,sK5),sK3) != iProver_top
    | v2_struct_0(sK2(sK3,sK4,sK5)) = iProver_top
    | v4_orders_2(sK2(sK3,sK4,sK5)) != iProver_top
    | v7_waybel_0(sK2(sK3,sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4949,c_2275])).

cnf(c_2625,plain,
    ( ~ m2_yellow_6(sK2(sK3,sK4,X0_50),sK3,sK4)
    | ~ l1_waybel_0(sK4,sK3)
    | v2_struct_0(sK4)
    | v4_orders_2(sK2(sK3,sK4,X0_50))
    | ~ v4_orders_2(sK4)
    | ~ v7_waybel_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2511])).

cnf(c_2626,plain,
    ( m2_yellow_6(sK2(sK3,sK4,X0_50),sK3,sK4) != iProver_top
    | l1_waybel_0(sK4,sK3) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK2(sK3,sK4,X0_50)) = iProver_top
    | v4_orders_2(sK4) != iProver_top
    | v7_waybel_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2625])).

cnf(c_2628,plain,
    ( m2_yellow_6(sK2(sK3,sK4,sK5),sK3,sK4) != iProver_top
    | l1_waybel_0(sK4,sK3) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK2(sK3,sK4,sK5)) = iProver_top
    | v4_orders_2(sK4) != iProver_top
    | v7_waybel_0(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2626])).

cnf(c_2624,plain,
    ( ~ m2_yellow_6(sK2(sK3,sK4,X0_50),sK3,sK4)
    | ~ l1_waybel_0(sK4,sK3)
    | v2_struct_0(sK4)
    | ~ v4_orders_2(sK4)
    | v7_waybel_0(sK2(sK3,sK4,X0_50))
    | ~ v7_waybel_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2516])).

cnf(c_2630,plain,
    ( m2_yellow_6(sK2(sK3,sK4,X0_50),sK3,sK4) != iProver_top
    | l1_waybel_0(sK4,sK3) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK4) != iProver_top
    | v7_waybel_0(sK2(sK3,sK4,X0_50)) = iProver_top
    | v7_waybel_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2624])).

cnf(c_2632,plain,
    ( m2_yellow_6(sK2(sK3,sK4,sK5),sK3,sK4) != iProver_top
    | l1_waybel_0(sK4,sK3) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK4) != iProver_top
    | v7_waybel_0(sK2(sK3,sK4,sK5)) = iProver_top
    | v7_waybel_0(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2630])).

cnf(c_2623,plain,
    ( ~ m2_yellow_6(sK2(sK3,sK4,X0_50),sK3,sK4)
    | l1_waybel_0(sK2(sK3,sK4,X0_50),sK3)
    | ~ l1_waybel_0(sK4,sK3)
    | v2_struct_0(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v7_waybel_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2521])).

cnf(c_2634,plain,
    ( m2_yellow_6(sK2(sK3,sK4,X0_50),sK3,sK4) != iProver_top
    | l1_waybel_0(sK2(sK3,sK4,X0_50),sK3) = iProver_top
    | l1_waybel_0(sK4,sK3) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK4) != iProver_top
    | v7_waybel_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2623])).

cnf(c_2636,plain,
    ( m2_yellow_6(sK2(sK3,sK4,sK5),sK3,sK4) != iProver_top
    | l1_waybel_0(sK2(sK3,sK4,sK5),sK3) = iProver_top
    | l1_waybel_0(sK4,sK3) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK4) != iProver_top
    | v7_waybel_0(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2634])).

cnf(c_5127,plain,
    ( r3_waybel_9(sK3,sK2(sK3,sK4,sK5),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4954,c_30,c_31,c_32,c_33,c_37,c_39,c_2539,c_2628,c_2632,c_2636,c_3536])).

cnf(c_8,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_537,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_23])).

cnf(c_538,plain,
    ( ~ r3_waybel_9(sK3,X0,X1)
    | r2_hidden(X1,k10_yellow_6(sK3,sK1(sK3,X0,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l1_waybel_0(X0,sK3)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_537])).

cnf(c_542,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK3,X0,X1)
    | r2_hidden(X1,k10_yellow_6(sK3,sK1(sK3,X0,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l1_waybel_0(X0,sK3)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_538,c_24,c_20])).

cnf(c_543,plain,
    ( ~ r3_waybel_9(sK3,X0,X1)
    | r2_hidden(X1,k10_yellow_6(sK3,sK1(sK3,X0,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l1_waybel_0(X0,sK3)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_542])).

cnf(c_1824,plain,
    ( ~ r3_waybel_9(sK3,X0_49,X0_50)
    | r2_hidden(X0_50,k10_yellow_6(sK3,sK1(sK3,X0_49,X0_50)))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK3))
    | ~ l1_waybel_0(X0_49,sK3)
    | v2_struct_0(X0_49)
    | ~ v4_orders_2(X0_49)
    | ~ v7_waybel_0(X0_49) ),
    inference(subtyping,[status(esa)],[c_543])).

cnf(c_2278,plain,
    ( r3_waybel_9(sK3,X0_49,X0_50) != iProver_top
    | r2_hidden(X0_50,k10_yellow_6(sK3,sK1(sK3,X0_49,X0_50))) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | l1_waybel_0(X0_49,sK3) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v4_orders_2(X0_49) != iProver_top
    | v7_waybel_0(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1824])).

cnf(c_9,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | m2_yellow_6(sK1(X0,X1,X2),X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_504,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | m2_yellow_6(sK1(X0,X1,X2),X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_23])).

cnf(c_505,plain,
    ( ~ r3_waybel_9(sK3,X0,X1)
    | m2_yellow_6(sK1(sK3,X0,X1),sK3,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
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
    | m2_yellow_6(sK1(sK3,X0,X1),sK3,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l1_waybel_0(X0,sK3)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_505,c_24,c_20])).

cnf(c_510,plain,
    ( ~ r3_waybel_9(sK3,X0,X1)
    | m2_yellow_6(sK1(sK3,X0,X1),sK3,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l1_waybel_0(X0,sK3)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_509])).

cnf(c_1825,plain,
    ( ~ r3_waybel_9(sK3,X0_49,X0_50)
    | m2_yellow_6(sK1(sK3,X0_49,X0_50),sK3,X0_49)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK3))
    | ~ l1_waybel_0(X0_49,sK3)
    | v2_struct_0(X0_49)
    | ~ v4_orders_2(X0_49)
    | ~ v7_waybel_0(X0_49) ),
    inference(subtyping,[status(esa)],[c_510])).

cnf(c_2277,plain,
    ( r3_waybel_9(sK3,X0_49,X0_50) != iProver_top
    | m2_yellow_6(sK1(sK3,X0_49,X0_50),sK3,X0_49) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | l1_waybel_0(X0_49,sK3) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v4_orders_2(X0_49) != iProver_top
    | v7_waybel_0(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1825])).

cnf(c_10,plain,
    ( ~ m2_yellow_6(X0,X1,sK2(X1,X2,X3))
    | ~ r2_hidden(X3,k10_yellow_6(X1,X0))
    | r2_hidden(X3,k10_yellow_6(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_602,plain,
    ( ~ m2_yellow_6(X0,X1,sK2(X1,X2,X3))
    | ~ r2_hidden(X3,k10_yellow_6(X1,X0))
    | r2_hidden(X3,k10_yellow_6(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_23])).

cnf(c_603,plain,
    ( ~ m2_yellow_6(X0,sK3,sK2(sK3,X1,X2))
    | ~ r2_hidden(X2,k10_yellow_6(sK3,X0))
    | r2_hidden(X2,k10_yellow_6(sK3,X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
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
    | ~ m2_yellow_6(X0,sK3,sK2(sK3,X1,X2))
    | ~ r2_hidden(X2,k10_yellow_6(sK3,X0))
    | r2_hidden(X2,k10_yellow_6(sK3,X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ l1_waybel_0(X1,sK3)
    | v2_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_603,c_24,c_20])).

cnf(c_606,plain,
    ( ~ m2_yellow_6(X0,sK3,sK2(sK3,X1,X2))
    | ~ r2_hidden(X2,k10_yellow_6(sK3,X0))
    | r2_hidden(X2,k10_yellow_6(sK3,X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ l1_waybel_0(X1,sK3)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_605])).

cnf(c_1822,plain,
    ( ~ m2_yellow_6(X0_49,sK3,sK2(sK3,X1_49,X0_50))
    | ~ r2_hidden(X0_50,k10_yellow_6(sK3,X0_49))
    | r2_hidden(X0_50,k10_yellow_6(sK3,X1_49))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK3))
    | ~ l1_waybel_0(X1_49,sK3)
    | v2_struct_0(X1_49)
    | ~ v4_orders_2(X1_49)
    | ~ v7_waybel_0(X1_49) ),
    inference(subtyping,[status(esa)],[c_606])).

cnf(c_2280,plain,
    ( m2_yellow_6(X0_49,sK3,sK2(sK3,X1_49,X0_50)) != iProver_top
    | r2_hidden(X0_50,k10_yellow_6(sK3,X0_49)) != iProver_top
    | r2_hidden(X0_50,k10_yellow_6(sK3,X1_49)) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | l1_waybel_0(X1_49,sK3) != iProver_top
    | v2_struct_0(X1_49) = iProver_top
    | v4_orders_2(X1_49) != iProver_top
    | v7_waybel_0(X1_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1822])).

cnf(c_3315,plain,
    ( r3_waybel_9(sK3,sK2(sK3,X0_49,X0_50),X1_50) != iProver_top
    | r2_hidden(X0_50,k10_yellow_6(sK3,X0_49)) = iProver_top
    | r2_hidden(X0_50,k10_yellow_6(sK3,sK1(sK3,sK2(sK3,X0_49,X0_50),X1_50))) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | l1_waybel_0(X0_49,sK3) != iProver_top
    | l1_waybel_0(sK2(sK3,X0_49,X0_50),sK3) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v2_struct_0(sK2(sK3,X0_49,X0_50)) = iProver_top
    | v4_orders_2(X0_49) != iProver_top
    | v4_orders_2(sK2(sK3,X0_49,X0_50)) != iProver_top
    | v7_waybel_0(X0_49) != iProver_top
    | v7_waybel_0(sK2(sK3,X0_49,X0_50)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2277,c_2280])).

cnf(c_3028,plain,
    ( r2_hidden(X0_50,k10_yellow_6(sK3,X0_49)) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | l1_waybel_0(X0_49,sK3) != iProver_top
    | l1_waybel_0(sK2(sK3,X0_49,X0_50),sK3) = iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v4_orders_2(X0_49) != iProver_top
    | v7_waybel_0(X0_49) != iProver_top ),
    inference(superposition,[status(thm)],[c_2276,c_2281])).

cnf(c_3029,plain,
    ( r2_hidden(X0_50,k10_yellow_6(sK3,X0_49)) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | l1_waybel_0(X0_49,sK3) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v4_orders_2(X0_49) != iProver_top
    | v4_orders_2(sK2(sK3,X0_49,X0_50)) = iProver_top
    | v7_waybel_0(X0_49) != iProver_top ),
    inference(superposition,[status(thm)],[c_2276,c_2283])).

cnf(c_3030,plain,
    ( r2_hidden(X0_50,k10_yellow_6(sK3,X0_49)) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | l1_waybel_0(X0_49,sK3) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v4_orders_2(X0_49) != iProver_top
    | v7_waybel_0(X0_49) != iProver_top
    | v7_waybel_0(sK2(sK3,X0_49,X0_50)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2276,c_2282])).

cnf(c_3031,plain,
    ( r2_hidden(X0_50,k10_yellow_6(sK3,X0_49)) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | l1_waybel_0(X0_49,sK3) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v2_struct_0(sK2(sK3,X0_49,X0_50)) != iProver_top
    | v4_orders_2(X0_49) != iProver_top
    | v7_waybel_0(X0_49) != iProver_top ),
    inference(superposition,[status(thm)],[c_2276,c_2284])).

cnf(c_4616,plain,
    ( v7_waybel_0(X0_49) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | r3_waybel_9(sK3,sK2(sK3,X0_49,X0_50),X1_50) != iProver_top
    | r2_hidden(X0_50,k10_yellow_6(sK3,X0_49)) = iProver_top
    | r2_hidden(X0_50,k10_yellow_6(sK3,sK1(sK3,sK2(sK3,X0_49,X0_50),X1_50))) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | l1_waybel_0(X0_49,sK3) != iProver_top
    | v4_orders_2(X0_49) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3315,c_3028,c_3029,c_3030,c_3031])).

cnf(c_4617,plain,
    ( r3_waybel_9(sK3,sK2(sK3,X0_49,X0_50),X1_50) != iProver_top
    | r2_hidden(X0_50,k10_yellow_6(sK3,X0_49)) = iProver_top
    | r2_hidden(X0_50,k10_yellow_6(sK3,sK1(sK3,sK2(sK3,X0_49,X0_50),X1_50))) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | l1_waybel_0(X0_49,sK3) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v4_orders_2(X0_49) != iProver_top
    | v7_waybel_0(X0_49) != iProver_top ),
    inference(renaming,[status(thm)],[c_4616])).

cnf(c_4633,plain,
    ( r3_waybel_9(sK3,sK2(sK3,X0_49,X0_50),X0_50) != iProver_top
    | r2_hidden(X0_50,k10_yellow_6(sK3,X0_49)) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | l1_waybel_0(X0_49,sK3) != iProver_top
    | l1_waybel_0(sK2(sK3,X0_49,X0_50),sK3) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v2_struct_0(sK2(sK3,X0_49,X0_50)) = iProver_top
    | v4_orders_2(X0_49) != iProver_top
    | v4_orders_2(sK2(sK3,X0_49,X0_50)) != iProver_top
    | v7_waybel_0(X0_49) != iProver_top
    | v7_waybel_0(sK2(sK3,X0_49,X0_50)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2278,c_4617])).

cnf(c_5185,plain,
    ( v7_waybel_0(X0_49) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | r3_waybel_9(sK3,sK2(sK3,X0_49,X0_50),X0_50) != iProver_top
    | r2_hidden(X0_50,k10_yellow_6(sK3,X0_49)) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | l1_waybel_0(X0_49,sK3) != iProver_top
    | v4_orders_2(X0_49) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4633,c_3028,c_3029,c_3030,c_3031])).

cnf(c_5186,plain,
    ( r3_waybel_9(sK3,sK2(sK3,X0_49,X0_50),X0_50) != iProver_top
    | r2_hidden(X0_50,k10_yellow_6(sK3,X0_49)) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | l1_waybel_0(X0_49,sK3) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v4_orders_2(X0_49) != iProver_top
    | v7_waybel_0(X0_49) != iProver_top ),
    inference(renaming,[status(thm)],[c_5185])).

cnf(c_5198,plain,
    ( r2_hidden(sK5,k10_yellow_6(sK3,sK4)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | l1_waybel_0(sK4,sK3) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK4) != iProver_top
    | v7_waybel_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5127,c_5186])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5198,c_39,c_37,c_33,c_32,c_31,c_30])).


%------------------------------------------------------------------------------
