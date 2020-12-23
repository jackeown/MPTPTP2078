%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:57 EST 2020

% Result     : Theorem 0.86s
% Output     : CNFRefutation 0.86s
% Verified   : 
% Statistics : Number of formulae       :  294 (8060 expanded)
%              Number of clauses        :  190 (1673 expanded)
%              Number of leaves         :   23 (2662 expanded)
%              Depth                    :   43
%              Number of atoms          : 1824 (118984 expanded)
%              Number of equality atoms :  285 (7888 expanded)
%              Maximal formula depth    :   27 (   7 average)
%              Maximal clause size      :   38 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_yellow_0(X0,X1)
           => ( k1_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f45])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
        & r2_lattice3(X0,X1,sK0(X0,X1,X2))
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
                & r2_lattice3(X0,X1,sK0(X0,X1,X2))
                & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => ( l1_orders_2(X0)
        & l1_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => l1_orders_2(X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f37,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f84,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f14,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_waybel_2(X0,X2) != X1
              & r3_waybel_9(X0,X2,X1)
              & v10_waybel_0(X2,X0)
              & ! [X3] :
                  ( v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & l1_waybel_0(X2,X0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
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

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_waybel_2(X0,X2) != X1
              & r3_waybel_9(X0,X2,X1)
              & v10_waybel_0(X2,X0)
              & ! [X3] :
                  ( v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & l1_waybel_0(X2,X0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_waybel_9(X0)
      & v1_compts_1(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k1_waybel_2(X0,X2) != X1
          & r3_waybel_9(X0,X2,X1)
          & v10_waybel_0(X2,X0)
          & ! [X3] :
              ( v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & l1_waybel_0(X2,X0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
     => ( k1_waybel_2(X0,sK7) != X1
        & r3_waybel_9(X0,sK7,X1)
        & v10_waybel_0(sK7,X0)
        & ! [X3] :
            ( v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & l1_waybel_0(sK7,X0)
        & v7_waybel_0(sK7)
        & v4_orders_2(sK7)
        & ~ v2_struct_0(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_waybel_2(X0,X2) != X1
              & r3_waybel_9(X0,X2,X1)
              & v10_waybel_0(X2,X0)
              & ! [X3] :
                  ( v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & l1_waybel_0(X2,X0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_waybel_2(X0,X2) != sK6
            & r3_waybel_9(X0,X2,sK6)
            & v10_waybel_0(X2,X0)
            & ! [X3] :
                ( v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_waybel_2(X0,X2) != X1
                & r3_waybel_9(X0,X2,X1)
                & v10_waybel_0(X2,X0)
                & ! [X3] :
                    ( v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
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
          ( ? [X2] :
              ( k1_waybel_2(sK5,X2) != X1
              & r3_waybel_9(sK5,X2,X1)
              & v10_waybel_0(X2,sK5)
              & ! [X3] :
                  ( v5_pre_topc(k4_waybel_1(sK5,X3),sK5,sK5)
                  | ~ m1_subset_1(X3,u1_struct_0(sK5)) )
              & l1_waybel_0(X2,sK5)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(sK5)) )
      & l1_waybel_9(sK5)
      & v1_compts_1(sK5)
      & v2_lattice3(sK5)
      & v1_lattice3(sK5)
      & v5_orders_2(sK5)
      & v4_orders_2(sK5)
      & v3_orders_2(sK5)
      & v8_pre_topc(sK5)
      & v2_pre_topc(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( k1_waybel_2(sK5,sK7) != sK6
    & r3_waybel_9(sK5,sK7,sK6)
    & v10_waybel_0(sK7,sK5)
    & ! [X3] :
        ( v5_pre_topc(k4_waybel_1(sK5,X3),sK5,sK5)
        | ~ m1_subset_1(X3,u1_struct_0(sK5)) )
    & l1_waybel_0(sK7,sK5)
    & v7_waybel_0(sK7)
    & v4_orders_2(sK7)
    & ~ v2_struct_0(sK7)
    & m1_subset_1(sK6,u1_struct_0(sK5))
    & l1_waybel_9(sK5)
    & v1_compts_1(sK5)
    & v2_lattice3(sK5)
    & v1_lattice3(sK5)
    & v5_orders_2(sK5)
    & v4_orders_2(sK5)
    & v3_orders_2(sK5)
    & v8_pre_topc(sK5)
    & v2_pre_topc(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f43,f62,f61,f60])).

fof(f97,plain,(
    l1_waybel_9(sK5) ),
    inference(cnf_transformation,[],[f63])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | r2_lattice3(X0,X1,sK0(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f91,plain,(
    v3_orders_2(sK5) ),
    inference(cnf_transformation,[],[f63])).

fof(f94,plain,(
    v1_lattice3(sK5) ),
    inference(cnf_transformation,[],[f63])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f105,plain,(
    r3_waybel_9(sK5,sK7,sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f101,plain,(
    v7_waybel_0(sK7) ),
    inference(cnf_transformation,[],[f63])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(rectify,[],[f13])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f57,plain,(
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
    inference(rectify,[],[f41])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X5] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X5),X0,X0)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0)
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r3_orders_2(X0,X3,X4)
                      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ( ~ v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0)
                    & m1_subset_1(sK4(X0),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f57,f58])).

fof(f87,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r3_orders_2(X0,X3,X4)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | m1_subset_1(sK4(X0),u1_struct_0(X0))
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
    inference(cnf_transformation,[],[f59])).

fof(f112,plain,(
    ! [X4,X0,X3,X1] :
      ( r3_orders_2(X0,X3,X4)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | m1_subset_1(sK4(X0),u1_struct_0(X0))
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
    inference(equality_resolution,[],[f87])).

fof(f96,plain,(
    v1_compts_1(sK5) ),
    inference(cnf_transformation,[],[f63])).

fof(f89,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f63])).

fof(f90,plain,(
    v8_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f63])).

fof(f92,plain,(
    v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f63])).

fof(f93,plain,(
    v5_orders_2(sK5) ),
    inference(cnf_transformation,[],[f63])).

fof(f95,plain,(
    v2_lattice3(sK5) ),
    inference(cnf_transformation,[],[f63])).

fof(f99,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f63])).

fof(f100,plain,(
    v4_orders_2(sK7) ),
    inference(cnf_transformation,[],[f63])).

fof(f102,plain,(
    l1_waybel_0(sK7,sK5) ),
    inference(cnf_transformation,[],[f63])).

fof(f98,plain,(
    m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f63])).

fof(f88,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r3_orders_2(X0,X3,X4)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0)
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
    inference(cnf_transformation,[],[f59])).

fof(f111,plain,(
    ! [X4,X0,X3,X1] :
      ( r3_orders_2(X0,X3,X4)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0)
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
    inference(equality_resolution,[],[f88])).

fof(f103,plain,(
    ! [X3] :
      ( v5_pre_topc(k4_waybel_1(sK5,X3),sK5,sK5)
      | ~ m1_subset_1(X3,u1_struct_0(sK5)) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f66,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_yellow_0(X0,k2_relat_1(X1)) = k4_yellow_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_yellow_0(X0,k2_relat_1(X1)) = k4_yellow_2(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_yellow_0(X0,k2_relat_1(X1)) = k4_yellow_2(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_yellow_0(X0,k2_relat_1(X1)) = k4_yellow_2(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1))
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1))
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X4] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v10_waybel_0(X1,X0)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f55])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v10_waybel_0(X1,X0)
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
    inference(cnf_transformation,[],[f56])).

fof(f109,plain,(
    ! [X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v10_waybel_0(X1,X0)
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
    inference(equality_resolution,[],[f86])).

fof(f104,plain,(
    v10_waybel_0(sK7,sK5) ),
    inference(cnf_transformation,[],[f63])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v10_waybel_0(X1,X0)
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
    inference(cnf_transformation,[],[f56])).

fof(f110,plain,(
    ! [X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v10_waybel_0(X1,X0)
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
    inference(equality_resolution,[],[f85])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f51,plain,(
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
    inference(rectify,[],[f50])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( r1_orders_2(X0,X4,X5)
              | ~ r2_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ! [X5] :
            ( r1_orders_2(X0,sK2(X0,X1),X5)
            | ~ r2_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & r2_lattice3(X0,X1,sK2(X0,X1))
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
        & r2_lattice3(X0,X1,sK1(X0,X1,X2))
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ( ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
                  & r2_lattice3(X0,X1,sK1(X0,X1,X2))
                  & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( ! [X5] :
                  ( r1_orders_2(X0,sK2(X0,X1),X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,sK2(X0,X1))
              & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f51,f53,f52])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X1,sK1(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X1)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X1)
      | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f106,plain,(
    k1_waybel_2(sK5,sK7) != sK6 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_8,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_20,plain,
    ( ~ l1_waybel_9(X0)
    | l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_34,negated_conjecture,
    ( l1_waybel_9(sK5) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_693,plain,
    ( l1_orders_2(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_34])).

cnf(c_694,plain,
    ( l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_693])).

cnf(c_1304,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | k1_yellow_0(X0,X1) = X2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_694])).

cnf(c_1305,plain,
    ( ~ r2_lattice3(sK5,X0,X1)
    | ~ r1_yellow_0(sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | m1_subset_1(sK0(sK5,X0,X1),u1_struct_0(sK5))
    | k1_yellow_0(sK5,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1304])).

cnf(c_3461,plain,
    ( ~ r2_lattice3(sK5,X0_71,X0_69)
    | ~ r1_yellow_0(sK5,X0_71)
    | ~ m1_subset_1(X0_69,u1_struct_0(sK5))
    | m1_subset_1(sK0(sK5,X0_71,X0_69),u1_struct_0(sK5))
    | k1_yellow_0(sK5,X0_71) = X0_69 ),
    inference(subtyping,[status(esa)],[c_1305])).

cnf(c_3983,plain,
    ( k1_yellow_0(sK5,X0_71) = X0_69
    | r2_lattice3(sK5,X0_71,X0_69) != iProver_top
    | r1_yellow_0(sK5,X0_71) != iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK0(sK5,X0_71,X0_69),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3461])).

cnf(c_7,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK0(X0,X1,X2))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1325,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK0(X0,X1,X2))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k1_yellow_0(X0,X1) = X2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_694])).

cnf(c_1326,plain,
    ( ~ r2_lattice3(sK5,X0,X1)
    | r2_lattice3(sK5,X0,sK0(sK5,X0,X1))
    | ~ r1_yellow_0(sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k1_yellow_0(sK5,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1325])).

cnf(c_3460,plain,
    ( ~ r2_lattice3(sK5,X0_71,X0_69)
    | r2_lattice3(sK5,X0_71,sK0(sK5,X0_71,X0_69))
    | ~ r1_yellow_0(sK5,X0_71)
    | ~ m1_subset_1(X0_69,u1_struct_0(sK5))
    | k1_yellow_0(sK5,X0_71) = X0_69 ),
    inference(subtyping,[status(esa)],[c_1326])).

cnf(c_3984,plain,
    ( k1_yellow_0(sK5,X0_71) = X0_69
    | r2_lattice3(sK5,X0_71,X0_69) != iProver_top
    | r2_lattice3(sK5,X0_71,sK0(sK5,X0_71,X0_69)) = iProver_top
    | r1_yellow_0(sK5,X0_71) != iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3460])).

cnf(c_4,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_40,negated_conjecture,
    ( v3_orders_2(sK5) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_715,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_40])).

cnf(c_716,plain,
    ( r1_orders_2(sK5,X0,X1)
    | ~ r3_orders_2(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v2_struct_0(sK5)
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_715])).

cnf(c_37,negated_conjecture,
    ( v1_lattice3(sK5) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_75,plain,
    ( ~ l1_waybel_9(sK5)
    | l1_orders_2(sK5) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_5,plain,
    ( ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_120,plain,
    ( ~ v1_lattice3(sK5)
    | ~ v2_struct_0(sK5)
    | ~ l1_orders_2(sK5) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_720,plain,
    ( r1_orders_2(sK5,X0,X1)
    | ~ r3_orders_2(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_716,c_37,c_34,c_75,c_120])).

cnf(c_721,plain,
    ( r1_orders_2(sK5,X0,X1)
    | ~ r3_orders_2(sK5,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_720])).

cnf(c_26,negated_conjecture,
    ( r3_waybel_9(sK5,sK7,sK6) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_30,negated_conjecture,
    ( v7_waybel_0(sK7) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_24,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
    | r3_orders_2(X0,X2,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK4(X0),u1_struct_0(X0))
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
    inference(cnf_transformation,[],[f112])).

cnf(c_35,negated_conjecture,
    ( v1_compts_1(sK5) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_640,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
    | r3_orders_2(X0,X2,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | m1_subset_1(sK4(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v2_lattice3(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_35])).

cnf(c_641,plain,
    ( ~ r3_waybel_9(sK5,X0,X1)
    | ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK5),u1_waybel_0(sK5,X0)),X2)
    | r3_orders_2(sK5,X1,X2)
    | ~ l1_waybel_0(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | m1_subset_1(sK4(sK5),u1_struct_0(sK5))
    | ~ v2_pre_topc(sK5)
    | ~ v8_pre_topc(sK5)
    | ~ v2_lattice3(sK5)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK5)
    | ~ v7_waybel_0(X0)
    | ~ l1_waybel_9(sK5)
    | ~ v5_orders_2(sK5)
    | ~ v1_lattice3(sK5)
    | v2_struct_0(X0)
    | ~ v3_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_640])).

cnf(c_42,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_41,negated_conjecture,
    ( v8_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_39,negated_conjecture,
    ( v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_38,negated_conjecture,
    ( v5_orders_2(sK5) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_36,negated_conjecture,
    ( v2_lattice3(sK5) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_645,plain,
    ( v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK5,X0,X1)
    | ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK5),u1_waybel_0(sK5,X0)),X2)
    | r3_orders_2(sK5,X1,X2)
    | ~ l1_waybel_0(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | m1_subset_1(sK4(sK5),u1_struct_0(sK5))
    | ~ v7_waybel_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_641,c_42,c_41,c_40,c_39,c_38,c_37,c_36,c_34])).

cnf(c_646,plain,
    ( ~ r3_waybel_9(sK5,X0,X1)
    | ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK5),u1_waybel_0(sK5,X0)),X2)
    | r3_orders_2(sK5,X1,X2)
    | ~ l1_waybel_0(X0,sK5)
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | m1_subset_1(sK4(sK5),u1_struct_0(sK5))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_645])).

cnf(c_773,plain,
    ( ~ r3_waybel_9(sK5,X0,X1)
    | ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK5),u1_waybel_0(sK5,X0)),X2)
    | r3_orders_2(sK5,X1,X2)
    | ~ l1_waybel_0(X0,sK5)
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | m1_subset_1(sK4(sK5),u1_struct_0(sK5))
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_646])).

cnf(c_774,plain,
    ( ~ r3_waybel_9(sK5,sK7,X0)
    | ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X1)
    | r3_orders_2(sK5,X0,X1)
    | ~ l1_waybel_0(sK7,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(sK4(sK5),u1_struct_0(sK5))
    | ~ v4_orders_2(sK7)
    | v2_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_773])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_31,negated_conjecture,
    ( v4_orders_2(sK7) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_29,negated_conjecture,
    ( l1_waybel_0(sK7,sK5) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_778,plain,
    ( r3_orders_2(sK5,X0,X1)
    | ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X1)
    | ~ r3_waybel_9(sK5,sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(sK4(sK5),u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_774,c_32,c_31,c_29])).

cnf(c_779,plain,
    ( ~ r3_waybel_9(sK5,sK7,X0)
    | ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X1)
    | r3_orders_2(sK5,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | m1_subset_1(sK4(sK5),u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_778])).

cnf(c_970,plain,
    ( ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
    | r3_orders_2(sK5,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(sK4(sK5),u1_struct_0(sK5))
    | sK6 != X1
    | sK7 != sK7
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_779])).

cnf(c_971,plain,
    ( ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
    | r3_orders_2(sK5,sK6,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(sK4(sK5),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_970])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_975,plain,
    ( m1_subset_1(sK4(sK5),u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r3_orders_2(sK5,sK6,X0)
    | ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_971,c_33])).

cnf(c_976,plain,
    ( ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
    | r3_orders_2(sK5,sK6,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(sK4(sK5),u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_975])).

cnf(c_1048,plain,
    ( ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
    | r1_orders_2(sK5,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | m1_subset_1(sK4(sK5),u1_struct_0(sK5))
    | X0 != X2
    | sK6 != X1
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_721,c_976])).

cnf(c_1049,plain,
    ( ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
    | r1_orders_2(sK5,sK6,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(sK4(sK5),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_1048])).

cnf(c_1053,plain,
    ( m1_subset_1(sK4(sK5),u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r1_orders_2(sK5,sK6,X0)
    | ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1049,c_33])).

cnf(c_1054,plain,
    ( ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
    | r1_orders_2(sK5,sK6,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(sK4(sK5),u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_1053])).

cnf(c_3471,plain,
    ( ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0_69)
    | r1_orders_2(sK5,sK6,X0_69)
    | ~ m1_subset_1(X0_69,u1_struct_0(sK5))
    | m1_subset_1(sK4(sK5),u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_1054])).

cnf(c_3971,plain,
    ( r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0_69) != iProver_top
    | r1_orders_2(sK5,sK6,X0_69) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK4(sK5),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3471])).

cnf(c_3553,plain,
    ( r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0_69) != iProver_top
    | r1_orders_2(sK5,sK6,X0_69) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK4(sK5),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3471])).

cnf(c_23,plain,
    ( ~ v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0)
    | ~ r3_waybel_9(X0,X1,X2)
    | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
    | r3_orders_2(X0,X2,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
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
    inference(cnf_transformation,[],[f111])).

cnf(c_28,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(sK5,X0),sK5,sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_564,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
    | r3_orders_2(X0,X2,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(sK5))
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
    | k4_waybel_1(X0,sK4(X0)) != k4_waybel_1(sK5,X4)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_28])).

cnf(c_565,plain,
    ( ~ r3_waybel_9(sK5,X0,X1)
    | ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK5),u1_waybel_0(sK5,X0)),X2)
    | r3_orders_2(sK5,X1,X2)
    | ~ l1_waybel_0(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X3,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ v2_pre_topc(sK5)
    | ~ v8_pre_topc(sK5)
    | ~ v2_lattice3(sK5)
    | ~ v1_compts_1(sK5)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK5)
    | ~ v7_waybel_0(X0)
    | ~ l1_waybel_9(sK5)
    | ~ v5_orders_2(sK5)
    | ~ v1_lattice3(sK5)
    | v2_struct_0(X0)
    | ~ v3_orders_2(sK5)
    | k4_waybel_1(sK5,sK4(sK5)) != k4_waybel_1(sK5,X3) ),
    inference(unflattening,[status(thm)],[c_564])).

cnf(c_569,plain,
    ( v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(X3,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ l1_waybel_0(X0,sK5)
    | r3_orders_2(sK5,X1,X2)
    | ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK5),u1_waybel_0(sK5,X0)),X2)
    | ~ r3_waybel_9(sK5,X0,X1)
    | ~ v7_waybel_0(X0)
    | k4_waybel_1(sK5,sK4(sK5)) != k4_waybel_1(sK5,X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_565,c_42,c_41,c_40,c_39,c_38,c_37,c_36,c_35,c_34])).

cnf(c_570,plain,
    ( ~ r3_waybel_9(sK5,X0,X1)
    | ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK5),u1_waybel_0(sK5,X0)),X2)
    | r3_orders_2(sK5,X1,X2)
    | ~ l1_waybel_0(X0,sK5)
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(X3,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k4_waybel_1(sK5,sK4(sK5)) != k4_waybel_1(sK5,X3) ),
    inference(renaming,[status(thm)],[c_569])).

cnf(c_803,plain,
    ( ~ r3_waybel_9(sK5,X0,X1)
    | ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK5),u1_waybel_0(sK5,X0)),X2)
    | r3_orders_2(sK5,X1,X2)
    | ~ l1_waybel_0(X0,sK5)
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(X3,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k4_waybel_1(sK5,sK4(sK5)) != k4_waybel_1(sK5,X3)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_570])).

cnf(c_804,plain,
    ( ~ r3_waybel_9(sK5,sK7,X0)
    | ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X1)
    | r3_orders_2(sK5,X0,X1)
    | ~ l1_waybel_0(sK7,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ v4_orders_2(sK7)
    | v2_struct_0(sK7)
    | k4_waybel_1(sK5,sK4(sK5)) != k4_waybel_1(sK5,X2) ),
    inference(unflattening,[status(thm)],[c_803])).

cnf(c_808,plain,
    ( r3_orders_2(sK5,X0,X1)
    | ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X1)
    | ~ r3_waybel_9(sK5,sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k4_waybel_1(sK5,sK4(sK5)) != k4_waybel_1(sK5,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_804,c_32,c_31,c_29])).

cnf(c_809,plain,
    ( ~ r3_waybel_9(sK5,sK7,X0)
    | ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X1)
    | r3_orders_2(sK5,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k4_waybel_1(sK5,sK4(sK5)) != k4_waybel_1(sK5,X2) ),
    inference(renaming,[status(thm)],[c_808])).

cnf(c_943,plain,
    ( ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
    | r3_orders_2(sK5,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k4_waybel_1(sK5,sK4(sK5)) != k4_waybel_1(sK5,X2)
    | sK6 != X1
    | sK7 != sK7
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_809])).

cnf(c_944,plain,
    ( ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
    | r3_orders_2(sK5,sK6,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | k4_waybel_1(sK5,sK4(sK5)) != k4_waybel_1(sK5,X1) ),
    inference(unflattening,[status(thm)],[c_943])).

cnf(c_948,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r3_orders_2(sK5,sK6,X0)
    | ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
    | k4_waybel_1(sK5,sK4(sK5)) != k4_waybel_1(sK5,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_944,c_33])).

cnf(c_949,plain,
    ( ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
    | r3_orders_2(sK5,sK6,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k4_waybel_1(sK5,sK4(sK5)) != k4_waybel_1(sK5,X1) ),
    inference(renaming,[status(thm)],[c_948])).

cnf(c_1072,plain,
    ( ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
    | r1_orders_2(sK5,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X3,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | X0 != X2
    | k4_waybel_1(sK5,sK4(sK5)) != k4_waybel_1(sK5,X3)
    | sK6 != X1
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_721,c_949])).

cnf(c_1073,plain,
    ( ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
    | r1_orders_2(sK5,sK6,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | k4_waybel_1(sK5,sK4(sK5)) != k4_waybel_1(sK5,X1) ),
    inference(unflattening,[status(thm)],[c_1072])).

cnf(c_1077,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r1_orders_2(sK5,sK6,X0)
    | ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
    | k4_waybel_1(sK5,sK4(sK5)) != k4_waybel_1(sK5,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1073,c_33])).

cnf(c_1078,plain,
    ( ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
    | r1_orders_2(sK5,sK6,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k4_waybel_1(sK5,sK4(sK5)) != k4_waybel_1(sK5,X1) ),
    inference(renaming,[status(thm)],[c_1077])).

cnf(c_3470,plain,
    ( ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0_69)
    | r1_orders_2(sK5,sK6,X0_69)
    | ~ m1_subset_1(X1_69,u1_struct_0(sK5))
    | ~ m1_subset_1(X0_69,u1_struct_0(sK5))
    | k4_waybel_1(sK5,sK4(sK5)) != k4_waybel_1(sK5,X1_69) ),
    inference(subtyping,[status(esa)],[c_1078])).

cnf(c_3483,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_3470])).

cnf(c_3556,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3483])).

cnf(c_3482,plain,
    ( ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0_69)
    | r1_orders_2(sK5,sK6,X0_69)
    | ~ m1_subset_1(X0_69,u1_struct_0(sK5))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_3470])).

cnf(c_3557,plain,
    ( r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0_69) != iProver_top
    | r1_orders_2(sK5,sK6,X0_69) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3482])).

cnf(c_3481,plain,
    ( ~ m1_subset_1(X0_69,u1_struct_0(sK5))
    | k4_waybel_1(sK5,sK4(sK5)) != k4_waybel_1(sK5,X0_69)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_3470])).

cnf(c_3974,plain,
    ( k4_waybel_1(sK5,sK4(sK5)) != k4_waybel_1(sK5,X0_69)
    | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3481])).

cnf(c_4511,plain,
    ( m1_subset_1(sK4(sK5),u1_struct_0(sK5)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3974])).

cnf(c_4559,plain,
    ( m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top
    | r1_orders_2(sK5,sK6,X0_69) = iProver_top
    | r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0_69) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3971,c_3553,c_3556,c_3557,c_4511])).

cnf(c_4560,plain,
    ( r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0_69) != iProver_top
    | r1_orders_2(sK5,sK6,X0_69) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4559])).

cnf(c_17,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_465,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_orders_2(X2)
    | X2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_2])).

cnf(c_466,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(unflattening,[status(thm)],[c_465])).

cnf(c_851,plain,
    ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ l1_orders_2(X0)
    | sK7 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_466,c_29])).

cnf(c_852,plain,
    ( m1_subset_1(u1_waybel_0(sK5,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_851])).

cnf(c_854,plain,
    ( m1_subset_1(u1_waybel_0(sK5,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_852,c_34,c_75])).

cnf(c_3476,plain,
    ( m1_subset_1(u1_waybel_0(sK5,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) ),
    inference(subtyping,[status(esa)],[c_854])).

cnf(c_3967,plain,
    ( m1_subset_1(u1_waybel_0(sK5,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3476])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3479,plain,
    ( ~ m1_subset_1(X0_69,k1_zfmisc_1(k2_zfmisc_1(X0_72,X1_72)))
    | k2_relset_1(X0_72,X1_72,X0_69) = k2_relat_1(X0_69) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_3965,plain,
    ( k2_relset_1(X0_72,X1_72,X0_69) = k2_relat_1(X0_69)
    | m1_subset_1(X0_69,k1_zfmisc_1(k2_zfmisc_1(X0_72,X1_72))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3479])).

cnf(c_4247,plain,
    ( k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)) = k2_relat_1(u1_waybel_0(sK5,sK7)) ),
    inference(superposition,[status(thm)],[c_3967,c_3965])).

cnf(c_4565,plain,
    ( r2_lattice3(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69) != iProver_top
    | r1_orders_2(sK5,sK6,X0_69) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4560,c_4247])).

cnf(c_4692,plain,
    ( k1_yellow_0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7))) = X0_69
    | r2_lattice3(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69) != iProver_top
    | r1_orders_2(sK5,sK6,sK0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69)) = iProver_top
    | r1_yellow_0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7))) != iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69),u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3984,c_4565])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3480,plain,
    ( ~ m1_subset_1(X0_69,k1_zfmisc_1(k2_zfmisc_1(X0_72,X1_72)))
    | v1_relat_1(X0_69) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_3964,plain,
    ( m1_subset_1(X0_69,k1_zfmisc_1(k2_zfmisc_1(X0_72,X1_72))) != iProver_top
    | v1_relat_1(X0_69) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3480])).

cnf(c_4242,plain,
    ( v1_relat_1(u1_waybel_0(sK5,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3967,c_3964])).

cnf(c_19,plain,
    ( v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_relat_1(X1)
    | k1_yellow_0(X0,k2_relat_1(X1)) = k4_yellow_2(X0,X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_702,plain,
    ( ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_37])).

cnf(c_703,plain,
    ( ~ v2_struct_0(sK5)
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_702])).

cnf(c_705,plain,
    ( ~ v2_struct_0(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_703,c_37,c_34,c_75,c_120])).

cnf(c_888,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_relat_1(X1)
    | k1_yellow_0(X0,k2_relat_1(X1)) = k4_yellow_2(X0,X1)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_705])).

cnf(c_889,plain,
    ( ~ l1_orders_2(sK5)
    | ~ v1_relat_1(X0)
    | k1_yellow_0(sK5,k2_relat_1(X0)) = k4_yellow_2(sK5,X0) ),
    inference(unflattening,[status(thm)],[c_888])).

cnf(c_893,plain,
    ( ~ v1_relat_1(X0)
    | k1_yellow_0(sK5,k2_relat_1(X0)) = k4_yellow_2(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_889,c_34,c_75])).

cnf(c_3474,plain,
    ( ~ v1_relat_1(X0_69)
    | k1_yellow_0(sK5,k2_relat_1(X0_69)) = k4_yellow_2(sK5,X0_69) ),
    inference(subtyping,[status(esa)],[c_893])).

cnf(c_3968,plain,
    ( k1_yellow_0(sK5,k2_relat_1(X0_69)) = k4_yellow_2(sK5,X0_69)
    | v1_relat_1(X0_69) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3474])).

cnf(c_4470,plain,
    ( k1_yellow_0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7))) = k4_yellow_2(sK5,u1_waybel_0(sK5,sK7)) ),
    inference(superposition,[status(thm)],[c_4242,c_3968])).

cnf(c_18,plain,
    ( ~ l1_waybel_0(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | k4_yellow_2(X1,u1_waybel_0(X1,X0)) = k1_waybel_2(X1,X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_862,plain,
    ( v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k4_yellow_2(X0,u1_waybel_0(X0,X1)) = k1_waybel_2(X0,X1)
    | sK7 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_29])).

cnf(c_863,plain,
    ( v2_struct_0(sK5)
    | ~ l1_orders_2(sK5)
    | k4_yellow_2(sK5,u1_waybel_0(sK5,sK7)) = k1_waybel_2(sK5,sK7) ),
    inference(unflattening,[status(thm)],[c_862])).

cnf(c_865,plain,
    ( k4_yellow_2(sK5,u1_waybel_0(sK5,sK7)) = k1_waybel_2(sK5,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_863,c_37,c_34,c_75,c_120])).

cnf(c_3475,plain,
    ( k4_yellow_2(sK5,u1_waybel_0(sK5,sK7)) = k1_waybel_2(sK5,sK7) ),
    inference(subtyping,[status(esa)],[c_865])).

cnf(c_4471,plain,
    ( k1_yellow_0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7))) = k1_waybel_2(sK5,sK7) ),
    inference(light_normalisation,[status(thm)],[c_4470,c_3475])).

cnf(c_4693,plain,
    ( k1_waybel_2(sK5,sK7) = X0_69
    | r2_lattice3(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69) != iProver_top
    | r1_orders_2(sK5,sK6,sK0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69)) = iProver_top
    | r1_yellow_0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7))) != iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69),u1_struct_0(sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4692,c_4471])).

cnf(c_52,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_21,plain,
    ( ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
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
    inference(cnf_transformation,[],[f109])).

cnf(c_27,negated_conjecture,
    ( v10_waybel_0(sK7,sK5) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_530,plain,
    ( ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
    | ~ r3_waybel_9(X0,X1,X2)
    | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
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
    | ~ v3_orders_2(X0)
    | sK7 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_531,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK5,sK3(sK5)),sK5,sK5)
    | ~ r3_waybel_9(sK5,sK7,X0)
    | r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
    | ~ l1_waybel_0(sK7,sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ v2_pre_topc(sK5)
    | ~ v8_pre_topc(sK5)
    | ~ v2_lattice3(sK5)
    | ~ v1_compts_1(sK5)
    | ~ v4_orders_2(sK7)
    | ~ v4_orders_2(sK5)
    | ~ v7_waybel_0(sK7)
    | ~ l1_waybel_9(sK5)
    | ~ v5_orders_2(sK5)
    | ~ v1_lattice3(sK5)
    | v2_struct_0(sK7)
    | ~ v3_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_530])).

cnf(c_535,plain,
    ( r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
    | ~ r3_waybel_9(sK5,sK7,X0)
    | ~ v5_pre_topc(k4_waybel_1(sK5,sK3(sK5)),sK5,sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_531,c_42,c_41,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_32,c_31,c_30,c_29])).

cnf(c_536,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK5,sK3(sK5)),sK5,sK5)
    | ~ r3_waybel_9(sK5,sK7,X0)
    | r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_535])).

cnf(c_609,plain,
    ( ~ r3_waybel_9(sK5,sK7,X0)
    | r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k4_waybel_1(sK5,sK3(sK5)) != k4_waybel_1(sK5,X1)
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_536])).

cnf(c_994,plain,
    ( r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k4_waybel_1(sK5,sK3(sK5)) != k4_waybel_1(sK5,X1)
    | sK6 != X0
    | sK7 != sK7
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_609])).

cnf(c_995,plain,
    ( r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | k4_waybel_1(sK5,sK3(sK5)) != k4_waybel_1(sK5,X0) ),
    inference(unflattening,[status(thm)],[c_994])).

cnf(c_999,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),sK6)
    | k4_waybel_1(sK5,sK3(sK5)) != k4_waybel_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_995,c_33])).

cnf(c_1000,plain,
    ( r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k4_waybel_1(sK5,sK3(sK5)) != k4_waybel_1(sK5,X0) ),
    inference(renaming,[status(thm)],[c_999])).

cnf(c_3473,plain,
    ( r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),sK6)
    | ~ m1_subset_1(X0_69,u1_struct_0(sK5))
    | k4_waybel_1(sK5,sK3(sK5)) != k4_waybel_1(sK5,X0_69) ),
    inference(subtyping,[status(esa)],[c_1000])).

cnf(c_3969,plain,
    ( k4_waybel_1(sK5,sK3(sK5)) != k4_waybel_1(sK5,X0_69)
    | r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),sK6) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3473])).

cnf(c_22,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
    | ~ v10_waybel_0(X1,X0)
    | ~ l1_waybel_0(X1,X0)
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
    | ~ v3_orders_2(X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_506,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
    | ~ l1_waybel_0(X1,X0)
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
    | ~ v3_orders_2(X0)
    | sK7 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_27])).

cnf(c_507,plain,
    ( ~ r3_waybel_9(sK5,sK7,X0)
    | r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
    | ~ l1_waybel_0(sK7,sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(sK3(sK5),u1_struct_0(sK5))
    | ~ v2_pre_topc(sK5)
    | ~ v8_pre_topc(sK5)
    | ~ v2_lattice3(sK5)
    | ~ v1_compts_1(sK5)
    | ~ v4_orders_2(sK7)
    | ~ v4_orders_2(sK5)
    | ~ v7_waybel_0(sK7)
    | ~ l1_waybel_9(sK5)
    | ~ v5_orders_2(sK5)
    | ~ v1_lattice3(sK5)
    | v2_struct_0(sK7)
    | ~ v3_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_506])).

cnf(c_511,plain,
    ( r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
    | ~ r3_waybel_9(sK5,sK7,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(sK3(sK5),u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_507,c_42,c_41,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_32,c_31,c_30,c_29])).

cnf(c_512,plain,
    ( ~ r3_waybel_9(sK5,sK7,X0)
    | r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(sK3(sK5),u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_511])).

cnf(c_1015,plain,
    ( r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(sK3(sK5),u1_struct_0(sK5))
    | sK6 != X0
    | sK7 != sK7
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_512])).

cnf(c_1016,plain,
    ( r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),sK6)
    | m1_subset_1(sK3(sK5),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_1015])).

cnf(c_1018,plain,
    ( m1_subset_1(sK3(sK5),u1_struct_0(sK5))
    | r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1016,c_33])).

cnf(c_1019,plain,
    ( r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),sK6)
    | m1_subset_1(sK3(sK5),u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_1018])).

cnf(c_1020,plain,
    ( r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),sK6) = iProver_top
    | m1_subset_1(sK3(sK5),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1019])).

cnf(c_3489,plain,
    ( X0_73 = X0_73 ),
    theory(equality)).

cnf(c_4191,plain,
    ( k4_waybel_1(sK5,sK3(sK5)) = k4_waybel_1(sK5,sK3(sK5)) ),
    inference(instantiation,[status(thm)],[c_3489])).

cnf(c_4192,plain,
    ( r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),sK6)
    | ~ m1_subset_1(sK3(sK5),u1_struct_0(sK5))
    | k4_waybel_1(sK5,sK3(sK5)) != k4_waybel_1(sK5,sK3(sK5)) ),
    inference(instantiation,[status(thm)],[c_3473])).

cnf(c_4193,plain,
    ( k4_waybel_1(sK5,sK3(sK5)) != k4_waybel_1(sK5,sK3(sK5))
    | r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),sK6) = iProver_top
    | m1_subset_1(sK3(sK5),u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4192])).

cnf(c_4209,plain,
    ( r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3969,c_1020,c_4191,c_4193])).

cnf(c_4284,plain,
    ( r2_lattice3(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),sK6) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4247,c_4209])).

cnf(c_12,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK1(X0,X1,X2))
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1194,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK1(X0,X1,X2))
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_38])).

cnf(c_1195,plain,
    ( ~ r2_lattice3(sK5,X0,X1)
    | r2_lattice3(sK5,X0,sK1(sK5,X0,X1))
    | r1_yellow_0(sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_1194])).

cnf(c_1199,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r1_yellow_0(sK5,X0)
    | r2_lattice3(sK5,X0,sK1(sK5,X0,X1))
    | ~ r2_lattice3(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1195,c_34,c_75])).

cnf(c_1200,plain,
    ( ~ r2_lattice3(sK5,X0,X1)
    | r2_lattice3(sK5,X0,sK1(sK5,X0,X1))
    | r1_yellow_0(sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_1199])).

cnf(c_3465,plain,
    ( ~ r2_lattice3(sK5,X0_71,X0_69)
    | r2_lattice3(sK5,X0_71,sK1(sK5,X0_71,X0_69))
    | r1_yellow_0(sK5,X0_71)
    | ~ m1_subset_1(X0_69,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_1200])).

cnf(c_3979,plain,
    ( r2_lattice3(sK5,X0_71,X0_69) != iProver_top
    | r2_lattice3(sK5,X0_71,sK1(sK5,X0_71,X0_69)) = iProver_top
    | r1_yellow_0(sK5,X0_71) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3465])).

cnf(c_4572,plain,
    ( r2_lattice3(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69) != iProver_top
    | r1_orders_2(sK5,sK6,sK1(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69)) = iProver_top
    | r1_yellow_0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7))) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK1(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69),u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3979,c_4565])).

cnf(c_13,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1170,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_38])).

cnf(c_1171,plain,
    ( ~ r2_lattice3(sK5,X0,X1)
    | r1_yellow_0(sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | m1_subset_1(sK1(sK5,X0,X1),u1_struct_0(sK5))
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_1170])).

cnf(c_1175,plain,
    ( m1_subset_1(sK1(sK5,X0,X1),u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r1_yellow_0(sK5,X0)
    | ~ r2_lattice3(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1171,c_34,c_75])).

cnf(c_1176,plain,
    ( ~ r2_lattice3(sK5,X0,X1)
    | r1_yellow_0(sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | m1_subset_1(sK1(sK5,X0,X1),u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_1175])).

cnf(c_3466,plain,
    ( ~ r2_lattice3(sK5,X0_71,X0_69)
    | r1_yellow_0(sK5,X0_71)
    | ~ m1_subset_1(X0_69,u1_struct_0(sK5))
    | m1_subset_1(sK1(sK5,X0_71,X0_69),u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_1176])).

cnf(c_3978,plain,
    ( r2_lattice3(sK5,X0_71,X0_69) != iProver_top
    | r1_yellow_0(sK5,X0_71) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK1(sK5,X0_71,X0_69),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3466])).

cnf(c_5165,plain,
    ( r2_lattice3(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69) != iProver_top
    | r1_orders_2(sK5,sK6,sK1(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69)) = iProver_top
    | r1_yellow_0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7))) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4572,c_3978])).

cnf(c_11,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1218,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_38])).

cnf(c_1219,plain,
    ( ~ r2_lattice3(sK5,X0,X1)
    | ~ r1_orders_2(sK5,X1,sK1(sK5,X0,X1))
    | r1_yellow_0(sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_1218])).

cnf(c_1223,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r1_yellow_0(sK5,X0)
    | ~ r1_orders_2(sK5,X1,sK1(sK5,X0,X1))
    | ~ r2_lattice3(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1219,c_34,c_75])).

cnf(c_1224,plain,
    ( ~ r2_lattice3(sK5,X0,X1)
    | ~ r1_orders_2(sK5,X1,sK1(sK5,X0,X1))
    | r1_yellow_0(sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_1223])).

cnf(c_3464,plain,
    ( ~ r2_lattice3(sK5,X0_71,X0_69)
    | ~ r1_orders_2(sK5,X0_69,sK1(sK5,X0_71,X0_69))
    | r1_yellow_0(sK5,X0_71)
    | ~ m1_subset_1(X0_69,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_1224])).

cnf(c_3980,plain,
    ( r2_lattice3(sK5,X0_71,X0_69) != iProver_top
    | r1_orders_2(sK5,X0_69,sK1(sK5,X0_71,X0_69)) != iProver_top
    | r1_yellow_0(sK5,X0_71) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3464])).

cnf(c_5169,plain,
    ( r2_lattice3(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),sK6) != iProver_top
    | r1_yellow_0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7))) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5165,c_3980])).

cnf(c_5378,plain,
    ( r1_orders_2(sK5,sK6,sK0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69)) = iProver_top
    | r2_lattice3(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69) != iProver_top
    | k1_waybel_2(sK5,sK7) = X0_69
    | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69),u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4693,c_52,c_4284,c_5169])).

cnf(c_5379,plain,
    ( k1_waybel_2(sK5,sK7) = X0_69
    | r2_lattice3(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69) != iProver_top
    | r1_orders_2(sK5,sK6,sK0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69)) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69),u1_struct_0(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5378])).

cnf(c_5389,plain,
    ( k1_waybel_2(sK5,sK7) = X0_69
    | k1_yellow_0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7))) = X0_69
    | r2_lattice3(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69) != iProver_top
    | r1_orders_2(sK5,sK6,sK0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69)) = iProver_top
    | r1_yellow_0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7))) != iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3983,c_5379])).

cnf(c_5390,plain,
    ( k1_waybel_2(sK5,sK7) = X0_69
    | r2_lattice3(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69) != iProver_top
    | r1_orders_2(sK5,sK6,sK0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69)) = iProver_top
    | r1_yellow_0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7))) != iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5389,c_4471])).

cnf(c_5437,plain,
    ( r1_orders_2(sK5,sK6,sK0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69)) = iProver_top
    | r2_lattice3(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69) != iProver_top
    | k1_waybel_2(sK5,sK7) = X0_69
    | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5390,c_52,c_4284,c_5169])).

cnf(c_5438,plain,
    ( k1_waybel_2(sK5,sK7) = X0_69
    | r2_lattice3(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69) != iProver_top
    | r1_orders_2(sK5,sK6,sK0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69)) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5437])).

cnf(c_6,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1346,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k1_yellow_0(X0,X1) = X2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_694])).

cnf(c_1347,plain,
    ( ~ r2_lattice3(sK5,X0,X1)
    | ~ r1_orders_2(sK5,X1,sK0(sK5,X0,X1))
    | ~ r1_yellow_0(sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k1_yellow_0(sK5,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1346])).

cnf(c_3459,plain,
    ( ~ r2_lattice3(sK5,X0_71,X0_69)
    | ~ r1_orders_2(sK5,X0_69,sK0(sK5,X0_71,X0_69))
    | ~ r1_yellow_0(sK5,X0_71)
    | ~ m1_subset_1(X0_69,u1_struct_0(sK5))
    | k1_yellow_0(sK5,X0_71) = X0_69 ),
    inference(subtyping,[status(esa)],[c_1347])).

cnf(c_3985,plain,
    ( k1_yellow_0(sK5,X0_71) = X0_69
    | r2_lattice3(sK5,X0_71,X0_69) != iProver_top
    | r1_orders_2(sK5,X0_69,sK0(sK5,X0_71,X0_69)) != iProver_top
    | r1_yellow_0(sK5,X0_71) != iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3459])).

cnf(c_5447,plain,
    ( k1_waybel_2(sK5,sK7) = sK6
    | k1_yellow_0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7))) = sK6
    | r2_lattice3(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),sK6) != iProver_top
    | r1_yellow_0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7))) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5438,c_3985])).

cnf(c_5448,plain,
    ( k1_waybel_2(sK5,sK7) = sK6
    | r2_lattice3(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),sK6) != iProver_top
    | r1_yellow_0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7))) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5447,c_4471])).

cnf(c_25,negated_conjecture,
    ( k1_waybel_2(sK5,sK7) != sK6 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_3478,negated_conjecture,
    ( k1_waybel_2(sK5,sK7) != sK6 ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5448,c_5169,c_4284,c_3478,c_52])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:02:01 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 0.86/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.86/1.03  
% 0.86/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.86/1.03  
% 0.86/1.03  ------  iProver source info
% 0.86/1.03  
% 0.86/1.03  git: date: 2020-06-30 10:37:57 +0100
% 0.86/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.86/1.03  git: non_committed_changes: false
% 0.86/1.03  git: last_make_outside_of_git: false
% 0.86/1.03  
% 0.86/1.03  ------ 
% 0.86/1.03  
% 0.86/1.03  ------ Input Options
% 0.86/1.03  
% 0.86/1.03  --out_options                           all
% 0.86/1.03  --tptp_safe_out                         true
% 0.86/1.03  --problem_path                          ""
% 0.86/1.03  --include_path                          ""
% 0.86/1.03  --clausifier                            res/vclausify_rel
% 0.86/1.03  --clausifier_options                    --mode clausify
% 0.86/1.03  --stdin                                 false
% 0.86/1.03  --stats_out                             all
% 0.86/1.03  
% 0.86/1.03  ------ General Options
% 0.86/1.03  
% 0.86/1.03  --fof                                   false
% 0.86/1.03  --time_out_real                         305.
% 0.86/1.03  --time_out_virtual                      -1.
% 0.86/1.03  --symbol_type_check                     false
% 0.86/1.03  --clausify_out                          false
% 0.86/1.03  --sig_cnt_out                           false
% 0.86/1.03  --trig_cnt_out                          false
% 0.86/1.03  --trig_cnt_out_tolerance                1.
% 0.86/1.03  --trig_cnt_out_sk_spl                   false
% 0.86/1.03  --abstr_cl_out                          false
% 0.86/1.03  
% 0.86/1.03  ------ Global Options
% 0.86/1.03  
% 0.86/1.03  --schedule                              default
% 0.86/1.03  --add_important_lit                     false
% 0.86/1.03  --prop_solver_per_cl                    1000
% 0.86/1.03  --min_unsat_core                        false
% 0.86/1.03  --soft_assumptions                      false
% 0.86/1.03  --soft_lemma_size                       3
% 0.86/1.03  --prop_impl_unit_size                   0
% 0.86/1.03  --prop_impl_unit                        []
% 0.86/1.03  --share_sel_clauses                     true
% 0.86/1.03  --reset_solvers                         false
% 0.86/1.03  --bc_imp_inh                            [conj_cone]
% 0.86/1.03  --conj_cone_tolerance                   3.
% 0.86/1.03  --extra_neg_conj                        none
% 0.86/1.03  --large_theory_mode                     true
% 0.86/1.03  --prolific_symb_bound                   200
% 0.86/1.03  --lt_threshold                          2000
% 0.86/1.03  --clause_weak_htbl                      true
% 0.86/1.03  --gc_record_bc_elim                     false
% 0.86/1.03  
% 0.86/1.03  ------ Preprocessing Options
% 0.86/1.03  
% 0.86/1.03  --preprocessing_flag                    true
% 0.86/1.03  --time_out_prep_mult                    0.1
% 0.86/1.03  --splitting_mode                        input
% 0.86/1.03  --splitting_grd                         true
% 0.86/1.03  --splitting_cvd                         false
% 0.86/1.03  --splitting_cvd_svl                     false
% 0.86/1.03  --splitting_nvd                         32
% 0.86/1.03  --sub_typing                            true
% 0.86/1.03  --prep_gs_sim                           true
% 0.86/1.03  --prep_unflatten                        true
% 0.86/1.03  --prep_res_sim                          true
% 0.86/1.03  --prep_upred                            true
% 0.86/1.03  --prep_sem_filter                       exhaustive
% 0.86/1.03  --prep_sem_filter_out                   false
% 0.86/1.03  --pred_elim                             true
% 0.86/1.03  --res_sim_input                         true
% 0.86/1.03  --eq_ax_congr_red                       true
% 0.86/1.03  --pure_diseq_elim                       true
% 0.86/1.03  --brand_transform                       false
% 0.86/1.03  --non_eq_to_eq                          false
% 0.86/1.03  --prep_def_merge                        true
% 0.86/1.03  --prep_def_merge_prop_impl              false
% 0.86/1.03  --prep_def_merge_mbd                    true
% 0.86/1.03  --prep_def_merge_tr_red                 false
% 0.86/1.03  --prep_def_merge_tr_cl                  false
% 0.86/1.03  --smt_preprocessing                     true
% 0.86/1.03  --smt_ac_axioms                         fast
% 0.86/1.03  --preprocessed_out                      false
% 0.86/1.03  --preprocessed_stats                    false
% 0.86/1.03  
% 0.86/1.03  ------ Abstraction refinement Options
% 0.86/1.03  
% 0.86/1.03  --abstr_ref                             []
% 0.86/1.03  --abstr_ref_prep                        false
% 0.86/1.03  --abstr_ref_until_sat                   false
% 0.86/1.03  --abstr_ref_sig_restrict                funpre
% 0.86/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 0.86/1.03  --abstr_ref_under                       []
% 0.86/1.03  
% 0.86/1.03  ------ SAT Options
% 0.86/1.03  
% 0.86/1.03  --sat_mode                              false
% 0.86/1.03  --sat_fm_restart_options                ""
% 0.86/1.03  --sat_gr_def                            false
% 0.86/1.03  --sat_epr_types                         true
% 0.86/1.03  --sat_non_cyclic_types                  false
% 0.86/1.03  --sat_finite_models                     false
% 0.86/1.03  --sat_fm_lemmas                         false
% 0.86/1.03  --sat_fm_prep                           false
% 0.86/1.03  --sat_fm_uc_incr                        true
% 0.86/1.03  --sat_out_model                         small
% 0.86/1.03  --sat_out_clauses                       false
% 0.86/1.03  
% 0.86/1.03  ------ QBF Options
% 0.86/1.03  
% 0.86/1.03  --qbf_mode                              false
% 0.86/1.03  --qbf_elim_univ                         false
% 0.86/1.03  --qbf_dom_inst                          none
% 0.86/1.03  --qbf_dom_pre_inst                      false
% 0.86/1.03  --qbf_sk_in                             false
% 0.86/1.03  --qbf_pred_elim                         true
% 0.86/1.03  --qbf_split                             512
% 0.86/1.03  
% 0.86/1.03  ------ BMC1 Options
% 0.86/1.03  
% 0.86/1.03  --bmc1_incremental                      false
% 0.86/1.03  --bmc1_axioms                           reachable_all
% 0.86/1.03  --bmc1_min_bound                        0
% 0.86/1.03  --bmc1_max_bound                        -1
% 0.86/1.03  --bmc1_max_bound_default                -1
% 0.86/1.03  --bmc1_symbol_reachability              true
% 0.86/1.03  --bmc1_property_lemmas                  false
% 0.86/1.03  --bmc1_k_induction                      false
% 0.86/1.03  --bmc1_non_equiv_states                 false
% 0.86/1.03  --bmc1_deadlock                         false
% 0.86/1.03  --bmc1_ucm                              false
% 0.86/1.03  --bmc1_add_unsat_core                   none
% 0.86/1.03  --bmc1_unsat_core_children              false
% 0.86/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 0.86/1.03  --bmc1_out_stat                         full
% 0.86/1.03  --bmc1_ground_init                      false
% 0.86/1.03  --bmc1_pre_inst_next_state              false
% 0.86/1.03  --bmc1_pre_inst_state                   false
% 0.86/1.03  --bmc1_pre_inst_reach_state             false
% 0.86/1.03  --bmc1_out_unsat_core                   false
% 0.86/1.03  --bmc1_aig_witness_out                  false
% 0.86/1.03  --bmc1_verbose                          false
% 0.86/1.03  --bmc1_dump_clauses_tptp                false
% 0.86/1.03  --bmc1_dump_unsat_core_tptp             false
% 0.86/1.03  --bmc1_dump_file                        -
% 0.86/1.03  --bmc1_ucm_expand_uc_limit              128
% 0.86/1.03  --bmc1_ucm_n_expand_iterations          6
% 0.86/1.03  --bmc1_ucm_extend_mode                  1
% 0.86/1.03  --bmc1_ucm_init_mode                    2
% 0.86/1.03  --bmc1_ucm_cone_mode                    none
% 0.86/1.03  --bmc1_ucm_reduced_relation_type        0
% 0.86/1.03  --bmc1_ucm_relax_model                  4
% 0.86/1.03  --bmc1_ucm_full_tr_after_sat            true
% 0.86/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 0.86/1.03  --bmc1_ucm_layered_model                none
% 0.86/1.03  --bmc1_ucm_max_lemma_size               10
% 0.86/1.03  
% 0.86/1.03  ------ AIG Options
% 0.86/1.03  
% 0.86/1.03  --aig_mode                              false
% 0.86/1.03  
% 0.86/1.03  ------ Instantiation Options
% 0.86/1.03  
% 0.86/1.03  --instantiation_flag                    true
% 0.86/1.03  --inst_sos_flag                         false
% 0.86/1.03  --inst_sos_phase                        true
% 0.86/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.86/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.86/1.03  --inst_lit_sel_side                     num_symb
% 0.86/1.03  --inst_solver_per_active                1400
% 0.86/1.03  --inst_solver_calls_frac                1.
% 0.86/1.03  --inst_passive_queue_type               priority_queues
% 0.86/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.86/1.03  --inst_passive_queues_freq              [25;2]
% 0.86/1.03  --inst_dismatching                      true
% 0.86/1.03  --inst_eager_unprocessed_to_passive     true
% 0.86/1.03  --inst_prop_sim_given                   true
% 0.86/1.03  --inst_prop_sim_new                     false
% 0.86/1.03  --inst_subs_new                         false
% 0.86/1.03  --inst_eq_res_simp                      false
% 0.86/1.03  --inst_subs_given                       false
% 0.86/1.03  --inst_orphan_elimination               true
% 0.86/1.03  --inst_learning_loop_flag               true
% 0.86/1.03  --inst_learning_start                   3000
% 0.86/1.03  --inst_learning_factor                  2
% 0.86/1.03  --inst_start_prop_sim_after_learn       3
% 0.86/1.03  --inst_sel_renew                        solver
% 0.86/1.03  --inst_lit_activity_flag                true
% 0.86/1.03  --inst_restr_to_given                   false
% 0.86/1.03  --inst_activity_threshold               500
% 0.86/1.03  --inst_out_proof                        true
% 0.86/1.03  
% 0.86/1.03  ------ Resolution Options
% 0.86/1.03  
% 0.86/1.03  --resolution_flag                       true
% 0.86/1.03  --res_lit_sel                           adaptive
% 0.86/1.03  --res_lit_sel_side                      none
% 0.86/1.03  --res_ordering                          kbo
% 0.86/1.03  --res_to_prop_solver                    active
% 0.86/1.03  --res_prop_simpl_new                    false
% 0.86/1.03  --res_prop_simpl_given                  true
% 0.86/1.03  --res_passive_queue_type                priority_queues
% 0.86/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.86/1.03  --res_passive_queues_freq               [15;5]
% 0.86/1.03  --res_forward_subs                      full
% 0.86/1.03  --res_backward_subs                     full
% 0.86/1.03  --res_forward_subs_resolution           true
% 0.86/1.03  --res_backward_subs_resolution          true
% 0.86/1.03  --res_orphan_elimination                true
% 0.86/1.03  --res_time_limit                        2.
% 0.86/1.03  --res_out_proof                         true
% 0.86/1.03  
% 0.86/1.03  ------ Superposition Options
% 0.86/1.03  
% 0.86/1.03  --superposition_flag                    true
% 0.86/1.03  --sup_passive_queue_type                priority_queues
% 0.86/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.86/1.03  --sup_passive_queues_freq               [8;1;4]
% 0.86/1.03  --demod_completeness_check              fast
% 0.86/1.03  --demod_use_ground                      true
% 0.86/1.03  --sup_to_prop_solver                    passive
% 0.86/1.03  --sup_prop_simpl_new                    true
% 0.86/1.03  --sup_prop_simpl_given                  true
% 0.86/1.03  --sup_fun_splitting                     false
% 0.86/1.03  --sup_smt_interval                      50000
% 0.86/1.03  
% 0.86/1.03  ------ Superposition Simplification Setup
% 0.86/1.03  
% 0.86/1.03  --sup_indices_passive                   []
% 0.86/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.86/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.86/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.86/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 0.86/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.86/1.03  --sup_full_bw                           [BwDemod]
% 0.86/1.03  --sup_immed_triv                        [TrivRules]
% 0.86/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.86/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.86/1.03  --sup_immed_bw_main                     []
% 0.86/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.86/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 0.86/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.86/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.86/1.03  
% 0.86/1.03  ------ Combination Options
% 0.86/1.03  
% 0.86/1.03  --comb_res_mult                         3
% 0.86/1.03  --comb_sup_mult                         2
% 0.86/1.03  --comb_inst_mult                        10
% 0.86/1.03  
% 0.86/1.03  ------ Debug Options
% 0.86/1.03  
% 0.86/1.03  --dbg_backtrace                         false
% 0.86/1.03  --dbg_dump_prop_clauses                 false
% 0.86/1.03  --dbg_dump_prop_clauses_file            -
% 0.86/1.03  --dbg_out_stat                          false
% 0.86/1.03  ------ Parsing...
% 0.86/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.86/1.03  
% 0.86/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe:16:0s pe_e  sf_s  rm: 16 0s  sf_e  pe_s  pe_e 
% 0.86/1.03  
% 0.86/1.03  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.86/1.03  
% 0.86/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.86/1.03  ------ Proving...
% 0.86/1.03  ------ Problem Properties 
% 0.86/1.03  
% 0.86/1.03  
% 0.86/1.03  clauses                                 25
% 0.86/1.03  conjectures                             2
% 0.86/1.03  EPR                                     1
% 0.86/1.03  Horn                                    18
% 0.86/1.03  unary                                   4
% 0.86/1.03  binary                                  7
% 0.86/1.03  lits                                    74
% 0.86/1.03  lits eq                                 11
% 0.86/1.03  fd_pure                                 0
% 0.86/1.03  fd_pseudo                               0
% 0.86/1.03  fd_cond                                 0
% 0.86/1.03  fd_pseudo_cond                          3
% 0.86/1.03  AC symbols                              0
% 0.86/1.03  
% 0.86/1.03  ------ Schedule dynamic 5 is on 
% 0.86/1.03  
% 0.86/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.86/1.03  
% 0.86/1.03  
% 0.86/1.03  ------ 
% 0.86/1.03  Current options:
% 0.86/1.03  ------ 
% 0.86/1.03  
% 0.86/1.03  ------ Input Options
% 0.86/1.03  
% 0.86/1.03  --out_options                           all
% 0.86/1.03  --tptp_safe_out                         true
% 0.86/1.03  --problem_path                          ""
% 0.86/1.03  --include_path                          ""
% 0.86/1.03  --clausifier                            res/vclausify_rel
% 0.86/1.03  --clausifier_options                    --mode clausify
% 0.86/1.03  --stdin                                 false
% 0.86/1.03  --stats_out                             all
% 0.86/1.03  
% 0.86/1.03  ------ General Options
% 0.86/1.03  
% 0.86/1.03  --fof                                   false
% 0.86/1.03  --time_out_real                         305.
% 0.86/1.03  --time_out_virtual                      -1.
% 0.86/1.03  --symbol_type_check                     false
% 0.86/1.03  --clausify_out                          false
% 0.86/1.03  --sig_cnt_out                           false
% 0.86/1.03  --trig_cnt_out                          false
% 0.86/1.03  --trig_cnt_out_tolerance                1.
% 0.86/1.03  --trig_cnt_out_sk_spl                   false
% 0.86/1.03  --abstr_cl_out                          false
% 0.86/1.03  
% 0.86/1.03  ------ Global Options
% 0.86/1.03  
% 0.86/1.03  --schedule                              default
% 0.86/1.03  --add_important_lit                     false
% 0.86/1.03  --prop_solver_per_cl                    1000
% 0.86/1.03  --min_unsat_core                        false
% 0.86/1.03  --soft_assumptions                      false
% 0.86/1.03  --soft_lemma_size                       3
% 0.86/1.03  --prop_impl_unit_size                   0
% 0.86/1.03  --prop_impl_unit                        []
% 0.86/1.03  --share_sel_clauses                     true
% 0.86/1.03  --reset_solvers                         false
% 0.86/1.03  --bc_imp_inh                            [conj_cone]
% 0.86/1.03  --conj_cone_tolerance                   3.
% 0.86/1.03  --extra_neg_conj                        none
% 0.86/1.03  --large_theory_mode                     true
% 0.86/1.03  --prolific_symb_bound                   200
% 0.86/1.03  --lt_threshold                          2000
% 0.86/1.03  --clause_weak_htbl                      true
% 0.86/1.03  --gc_record_bc_elim                     false
% 0.86/1.03  
% 0.86/1.03  ------ Preprocessing Options
% 0.86/1.03  
% 0.86/1.03  --preprocessing_flag                    true
% 0.86/1.03  --time_out_prep_mult                    0.1
% 0.86/1.03  --splitting_mode                        input
% 0.86/1.03  --splitting_grd                         true
% 0.86/1.03  --splitting_cvd                         false
% 0.86/1.03  --splitting_cvd_svl                     false
% 0.86/1.03  --splitting_nvd                         32
% 0.86/1.03  --sub_typing                            true
% 0.86/1.03  --prep_gs_sim                           true
% 0.86/1.03  --prep_unflatten                        true
% 0.86/1.03  --prep_res_sim                          true
% 0.86/1.03  --prep_upred                            true
% 0.86/1.03  --prep_sem_filter                       exhaustive
% 0.86/1.03  --prep_sem_filter_out                   false
% 0.86/1.03  --pred_elim                             true
% 0.86/1.03  --res_sim_input                         true
% 0.86/1.03  --eq_ax_congr_red                       true
% 0.86/1.03  --pure_diseq_elim                       true
% 0.86/1.03  --brand_transform                       false
% 0.86/1.03  --non_eq_to_eq                          false
% 0.86/1.03  --prep_def_merge                        true
% 0.86/1.03  --prep_def_merge_prop_impl              false
% 0.86/1.03  --prep_def_merge_mbd                    true
% 0.86/1.03  --prep_def_merge_tr_red                 false
% 0.86/1.03  --prep_def_merge_tr_cl                  false
% 0.86/1.03  --smt_preprocessing                     true
% 0.86/1.03  --smt_ac_axioms                         fast
% 0.86/1.03  --preprocessed_out                      false
% 0.86/1.03  --preprocessed_stats                    false
% 0.86/1.03  
% 0.86/1.03  ------ Abstraction refinement Options
% 0.86/1.03  
% 0.86/1.03  --abstr_ref                             []
% 0.86/1.03  --abstr_ref_prep                        false
% 0.86/1.03  --abstr_ref_until_sat                   false
% 0.86/1.03  --abstr_ref_sig_restrict                funpre
% 0.86/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 0.86/1.03  --abstr_ref_under                       []
% 0.86/1.03  
% 0.86/1.03  ------ SAT Options
% 0.86/1.03  
% 0.86/1.03  --sat_mode                              false
% 0.86/1.03  --sat_fm_restart_options                ""
% 0.86/1.03  --sat_gr_def                            false
% 0.86/1.03  --sat_epr_types                         true
% 0.86/1.03  --sat_non_cyclic_types                  false
% 0.86/1.03  --sat_finite_models                     false
% 0.86/1.03  --sat_fm_lemmas                         false
% 0.86/1.03  --sat_fm_prep                           false
% 0.86/1.03  --sat_fm_uc_incr                        true
% 0.86/1.03  --sat_out_model                         small
% 0.86/1.03  --sat_out_clauses                       false
% 0.86/1.03  
% 0.86/1.03  ------ QBF Options
% 0.86/1.03  
% 0.86/1.03  --qbf_mode                              false
% 0.86/1.03  --qbf_elim_univ                         false
% 0.86/1.03  --qbf_dom_inst                          none
% 0.86/1.03  --qbf_dom_pre_inst                      false
% 0.86/1.03  --qbf_sk_in                             false
% 0.86/1.03  --qbf_pred_elim                         true
% 0.86/1.03  --qbf_split                             512
% 0.86/1.03  
% 0.86/1.03  ------ BMC1 Options
% 0.86/1.03  
% 0.86/1.03  --bmc1_incremental                      false
% 0.86/1.03  --bmc1_axioms                           reachable_all
% 0.86/1.03  --bmc1_min_bound                        0
% 0.86/1.03  --bmc1_max_bound                        -1
% 0.86/1.03  --bmc1_max_bound_default                -1
% 0.86/1.03  --bmc1_symbol_reachability              true
% 0.86/1.03  --bmc1_property_lemmas                  false
% 0.86/1.03  --bmc1_k_induction                      false
% 0.86/1.03  --bmc1_non_equiv_states                 false
% 0.86/1.03  --bmc1_deadlock                         false
% 0.86/1.03  --bmc1_ucm                              false
% 0.86/1.03  --bmc1_add_unsat_core                   none
% 0.86/1.03  --bmc1_unsat_core_children              false
% 0.86/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 0.86/1.03  --bmc1_out_stat                         full
% 0.86/1.03  --bmc1_ground_init                      false
% 0.86/1.03  --bmc1_pre_inst_next_state              false
% 0.86/1.03  --bmc1_pre_inst_state                   false
% 0.86/1.03  --bmc1_pre_inst_reach_state             false
% 0.86/1.03  --bmc1_out_unsat_core                   false
% 0.86/1.03  --bmc1_aig_witness_out                  false
% 0.86/1.03  --bmc1_verbose                          false
% 0.86/1.03  --bmc1_dump_clauses_tptp                false
% 0.86/1.03  --bmc1_dump_unsat_core_tptp             false
% 0.86/1.03  --bmc1_dump_file                        -
% 0.86/1.03  --bmc1_ucm_expand_uc_limit              128
% 0.86/1.03  --bmc1_ucm_n_expand_iterations          6
% 0.86/1.03  --bmc1_ucm_extend_mode                  1
% 0.86/1.03  --bmc1_ucm_init_mode                    2
% 0.86/1.03  --bmc1_ucm_cone_mode                    none
% 0.86/1.03  --bmc1_ucm_reduced_relation_type        0
% 0.86/1.03  --bmc1_ucm_relax_model                  4
% 0.86/1.03  --bmc1_ucm_full_tr_after_sat            true
% 0.86/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 0.86/1.03  --bmc1_ucm_layered_model                none
% 0.86/1.03  --bmc1_ucm_max_lemma_size               10
% 0.86/1.03  
% 0.86/1.03  ------ AIG Options
% 0.86/1.03  
% 0.86/1.03  --aig_mode                              false
% 0.86/1.03  
% 0.86/1.03  ------ Instantiation Options
% 0.86/1.03  
% 0.86/1.03  --instantiation_flag                    true
% 0.86/1.03  --inst_sos_flag                         false
% 0.86/1.03  --inst_sos_phase                        true
% 0.86/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.86/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.86/1.03  --inst_lit_sel_side                     none
% 0.86/1.03  --inst_solver_per_active                1400
% 0.86/1.03  --inst_solver_calls_frac                1.
% 0.86/1.03  --inst_passive_queue_type               priority_queues
% 0.86/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.86/1.03  --inst_passive_queues_freq              [25;2]
% 0.86/1.03  --inst_dismatching                      true
% 0.86/1.03  --inst_eager_unprocessed_to_passive     true
% 0.86/1.03  --inst_prop_sim_given                   true
% 0.86/1.03  --inst_prop_sim_new                     false
% 0.86/1.03  --inst_subs_new                         false
% 0.86/1.03  --inst_eq_res_simp                      false
% 0.86/1.03  --inst_subs_given                       false
% 0.86/1.03  --inst_orphan_elimination               true
% 0.86/1.03  --inst_learning_loop_flag               true
% 0.86/1.03  --inst_learning_start                   3000
% 0.86/1.03  --inst_learning_factor                  2
% 0.86/1.03  --inst_start_prop_sim_after_learn       3
% 0.86/1.03  --inst_sel_renew                        solver
% 0.86/1.03  --inst_lit_activity_flag                true
% 0.86/1.03  --inst_restr_to_given                   false
% 0.86/1.03  --inst_activity_threshold               500
% 0.86/1.03  --inst_out_proof                        true
% 0.86/1.03  
% 0.86/1.03  ------ Resolution Options
% 0.86/1.03  
% 0.86/1.03  --resolution_flag                       false
% 0.86/1.03  --res_lit_sel                           adaptive
% 0.86/1.03  --res_lit_sel_side                      none
% 0.86/1.03  --res_ordering                          kbo
% 0.86/1.03  --res_to_prop_solver                    active
% 0.86/1.03  --res_prop_simpl_new                    false
% 0.86/1.03  --res_prop_simpl_given                  true
% 0.86/1.03  --res_passive_queue_type                priority_queues
% 0.86/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.86/1.03  --res_passive_queues_freq               [15;5]
% 0.86/1.03  --res_forward_subs                      full
% 0.86/1.03  --res_backward_subs                     full
% 0.86/1.03  --res_forward_subs_resolution           true
% 0.86/1.03  --res_backward_subs_resolution          true
% 0.86/1.03  --res_orphan_elimination                true
% 0.86/1.03  --res_time_limit                        2.
% 0.86/1.03  --res_out_proof                         true
% 0.86/1.03  
% 0.86/1.03  ------ Superposition Options
% 0.86/1.03  
% 0.86/1.03  --superposition_flag                    true
% 0.86/1.03  --sup_passive_queue_type                priority_queues
% 0.86/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.86/1.03  --sup_passive_queues_freq               [8;1;4]
% 0.86/1.03  --demod_completeness_check              fast
% 0.86/1.03  --demod_use_ground                      true
% 0.86/1.03  --sup_to_prop_solver                    passive
% 0.86/1.03  --sup_prop_simpl_new                    true
% 0.86/1.03  --sup_prop_simpl_given                  true
% 0.86/1.03  --sup_fun_splitting                     false
% 0.86/1.03  --sup_smt_interval                      50000
% 0.86/1.03  
% 0.86/1.03  ------ Superposition Simplification Setup
% 0.86/1.03  
% 0.86/1.03  --sup_indices_passive                   []
% 0.86/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.86/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.86/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.86/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 0.86/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.86/1.03  --sup_full_bw                           [BwDemod]
% 0.86/1.03  --sup_immed_triv                        [TrivRules]
% 0.86/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.86/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.86/1.03  --sup_immed_bw_main                     []
% 0.86/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.86/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 0.86/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.86/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.86/1.03  
% 0.86/1.03  ------ Combination Options
% 0.86/1.03  
% 0.86/1.03  --comb_res_mult                         3
% 0.86/1.03  --comb_sup_mult                         2
% 0.86/1.03  --comb_inst_mult                        10
% 0.86/1.03  
% 0.86/1.03  ------ Debug Options
% 0.86/1.03  
% 0.86/1.03  --dbg_backtrace                         false
% 0.86/1.03  --dbg_dump_prop_clauses                 false
% 0.86/1.03  --dbg_dump_prop_clauses_file            -
% 0.86/1.03  --dbg_out_stat                          false
% 0.86/1.03  
% 0.86/1.03  
% 0.86/1.03  
% 0.86/1.03  
% 0.86/1.03  ------ Proving...
% 0.86/1.03  
% 0.86/1.03  
% 0.86/1.03  % SZS status Theorem for theBenchmark.p
% 0.86/1.03  
% 0.86/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 0.86/1.03  
% 0.86/1.03  fof(f6,axiom,(
% 0.86/1.03    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 0.86/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.86/1.03  
% 0.86/1.03  fof(f27,plain,(
% 0.86/1.03    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.86/1.03    inference(ennf_transformation,[],[f6])).
% 0.86/1.03  
% 0.86/1.03  fof(f28,plain,(
% 0.86/1.03    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.86/1.03    inference(flattening,[],[f27])).
% 0.86/1.03  
% 0.86/1.03  fof(f45,plain,(
% 0.86/1.03    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.86/1.03    inference(nnf_transformation,[],[f28])).
% 0.86/1.03  
% 0.86/1.03  fof(f46,plain,(
% 0.86/1.03    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.86/1.03    inference(flattening,[],[f45])).
% 0.86/1.03  
% 0.86/1.03  fof(f47,plain,(
% 0.86/1.03    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.86/1.03    inference(rectify,[],[f46])).
% 0.86/1.03  
% 0.86/1.03  fof(f48,plain,(
% 0.86/1.03    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK0(X0,X1,X2)) & r2_lattice3(X0,X1,sK0(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 0.86/1.03    introduced(choice_axiom,[])).
% 0.86/1.03  
% 0.86/1.03  fof(f49,plain,(
% 0.86/1.03    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,X2,sK0(X0,X1,X2)) & r2_lattice3(X0,X1,sK0(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.86/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).
% 0.86/1.03  
% 0.86/1.03  fof(f72,plain,(
% 0.86/1.03    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X1) = X2 | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.86/1.03    inference(cnf_transformation,[],[f49])).
% 0.86/1.03  
% 0.86/1.03  fof(f11,axiom,(
% 0.86/1.03    ! [X0] : (l1_waybel_9(X0) => (l1_orders_2(X0) & l1_pre_topc(X0)))),
% 0.86/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.86/1.03  
% 0.86/1.03  fof(f17,plain,(
% 0.86/1.03    ! [X0] : (l1_waybel_9(X0) => l1_orders_2(X0))),
% 0.86/1.03    inference(pure_predicate_removal,[],[f11])).
% 0.86/1.03  
% 0.86/1.03  fof(f37,plain,(
% 0.86/1.03    ! [X0] : (l1_orders_2(X0) | ~l1_waybel_9(X0))),
% 0.86/1.03    inference(ennf_transformation,[],[f17])).
% 0.86/1.03  
% 0.86/1.03  fof(f84,plain,(
% 0.86/1.03    ( ! [X0] : (l1_orders_2(X0) | ~l1_waybel_9(X0)) )),
% 0.86/1.03    inference(cnf_transformation,[],[f37])).
% 0.86/1.03  
% 0.86/1.03  fof(f14,conjecture,(
% 0.86/1.03    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => ((r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0))) => k1_waybel_2(X0,X2) = X1))))),
% 0.86/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.86/1.03  
% 0.86/1.03  fof(f15,negated_conjecture,(
% 0.86/1.03    ~! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => ((r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0))) => k1_waybel_2(X0,X2) = X1))))),
% 0.86/1.03    inference(negated_conjecture,[],[f14])).
% 0.86/1.03  
% 0.86/1.03  fof(f42,plain,(
% 0.86/1.03    ? [X0] : (? [X1] : (? [X2] : ((k1_waybel_2(X0,X2) != X1 & (r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))))) & (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.86/1.03    inference(ennf_transformation,[],[f15])).
% 0.86/1.03  
% 0.86/1.03  fof(f43,plain,(
% 0.86/1.03    ? [X0] : (? [X1] : (? [X2] : (k1_waybel_2(X0,X2) != X1 & r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 0.86/1.03    inference(flattening,[],[f42])).
% 0.86/1.03  
% 0.86/1.03  fof(f62,plain,(
% 0.86/1.03    ( ! [X0,X1] : (? [X2] : (k1_waybel_2(X0,X2) != X1 & r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (k1_waybel_2(X0,sK7) != X1 & r3_waybel_9(X0,sK7,X1) & v10_waybel_0(sK7,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(sK7,X0) & v7_waybel_0(sK7) & v4_orders_2(sK7) & ~v2_struct_0(sK7))) )),
% 0.86/1.03    introduced(choice_axiom,[])).
% 0.86/1.03  
% 0.86/1.03  fof(f61,plain,(
% 0.86/1.03    ( ! [X0] : (? [X1] : (? [X2] : (k1_waybel_2(X0,X2) != X1 & r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_waybel_2(X0,X2) != sK6 & r3_waybel_9(X0,X2,sK6) & v10_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(sK6,u1_struct_0(X0)))) )),
% 0.86/1.03    introduced(choice_axiom,[])).
% 0.86/1.03  
% 0.86/1.03  fof(f60,plain,(
% 0.86/1.03    ? [X0] : (? [X1] : (? [X2] : (k1_waybel_2(X0,X2) != X1 & r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (k1_waybel_2(sK5,X2) != X1 & r3_waybel_9(sK5,X2,X1) & v10_waybel_0(X2,sK5) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK5,X3),sK5,sK5) | ~m1_subset_1(X3,u1_struct_0(sK5))) & l1_waybel_0(X2,sK5) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(sK5))) & l1_waybel_9(sK5) & v1_compts_1(sK5) & v2_lattice3(sK5) & v1_lattice3(sK5) & v5_orders_2(sK5) & v4_orders_2(sK5) & v3_orders_2(sK5) & v8_pre_topc(sK5) & v2_pre_topc(sK5))),
% 0.86/1.03    introduced(choice_axiom,[])).
% 0.86/1.03  
% 0.86/1.03  fof(f63,plain,(
% 0.86/1.03    ((k1_waybel_2(sK5,sK7) != sK6 & r3_waybel_9(sK5,sK7,sK6) & v10_waybel_0(sK7,sK5) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK5,X3),sK5,sK5) | ~m1_subset_1(X3,u1_struct_0(sK5))) & l1_waybel_0(sK7,sK5) & v7_waybel_0(sK7) & v4_orders_2(sK7) & ~v2_struct_0(sK7)) & m1_subset_1(sK6,u1_struct_0(sK5))) & l1_waybel_9(sK5) & v1_compts_1(sK5) & v2_lattice3(sK5) & v1_lattice3(sK5) & v5_orders_2(sK5) & v4_orders_2(sK5) & v3_orders_2(sK5) & v8_pre_topc(sK5) & v2_pre_topc(sK5)),
% 0.86/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f43,f62,f61,f60])).
% 0.86/1.03  
% 0.86/1.03  fof(f97,plain,(
% 0.86/1.03    l1_waybel_9(sK5)),
% 0.86/1.03    inference(cnf_transformation,[],[f63])).
% 0.86/1.03  
% 0.86/1.03  fof(f73,plain,(
% 0.86/1.03    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X1) = X2 | r2_lattice3(X0,X1,sK0(X0,X1,X2)) | ~r2_lattice3(X0,X1,X2) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.86/1.03    inference(cnf_transformation,[],[f49])).
% 0.86/1.03  
% 0.86/1.03  fof(f4,axiom,(
% 0.86/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.86/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.86/1.03  
% 0.86/1.03  fof(f23,plain,(
% 0.86/1.03    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.86/1.03    inference(ennf_transformation,[],[f4])).
% 0.86/1.03  
% 0.86/1.03  fof(f24,plain,(
% 0.86/1.03    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.86/1.03    inference(flattening,[],[f23])).
% 0.86/1.03  
% 0.86/1.03  fof(f44,plain,(
% 0.86/1.03    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.86/1.03    inference(nnf_transformation,[],[f24])).
% 0.86/1.03  
% 0.86/1.03  fof(f67,plain,(
% 0.86/1.03    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.86/1.03    inference(cnf_transformation,[],[f44])).
% 0.86/1.03  
% 0.86/1.03  fof(f91,plain,(
% 0.86/1.03    v3_orders_2(sK5)),
% 0.86/1.03    inference(cnf_transformation,[],[f63])).
% 0.86/1.03  
% 0.86/1.03  fof(f94,plain,(
% 0.86/1.03    v1_lattice3(sK5)),
% 0.86/1.03    inference(cnf_transformation,[],[f63])).
% 0.86/1.03  
% 0.86/1.03  fof(f5,axiom,(
% 0.86/1.03    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.86/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.86/1.03  
% 0.86/1.03  fof(f25,plain,(
% 0.86/1.03    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.86/1.03    inference(ennf_transformation,[],[f5])).
% 0.86/1.03  
% 0.86/1.03  fof(f26,plain,(
% 0.86/1.03    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 0.86/1.03    inference(flattening,[],[f25])).
% 0.86/1.03  
% 0.86/1.03  fof(f69,plain,(
% 0.86/1.03    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 0.86/1.03    inference(cnf_transformation,[],[f26])).
% 0.86/1.03  
% 0.86/1.03  fof(f105,plain,(
% 0.86/1.03    r3_waybel_9(sK5,sK7,sK6)),
% 0.86/1.03    inference(cnf_transformation,[],[f63])).
% 0.86/1.03  
% 0.86/1.03  fof(f101,plain,(
% 0.86/1.03    v7_waybel_0(sK7)),
% 0.86/1.03    inference(cnf_transformation,[],[f63])).
% 0.86/1.03  
% 0.86/1.03  fof(f13,axiom,(
% 0.86/1.03    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) => r3_orders_2(X0,X3,X4))))))))),
% 0.86/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.86/1.03  
% 0.86/1.03  fof(f16,plain,(
% 0.86/1.03    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) => r3_orders_2(X0,X3,X5))))))))),
% 0.86/1.03    inference(rectify,[],[f13])).
% 0.86/1.03  
% 0.86/1.03  fof(f40,plain,(
% 0.86/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X5] : ((r3_orders_2(X0,X3,X5) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)) | ~m1_subset_1(X5,u1_struct_0(X0))) | (~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.86/1.03    inference(ennf_transformation,[],[f16])).
% 0.86/1.03  
% 0.86/1.03  fof(f41,plain,(
% 0.86/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X5] : (r3_orders_2(X0,X3,X5) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.86/1.03    inference(flattening,[],[f40])).
% 0.86/1.03  
% 0.86/1.03  fof(f57,plain,(
% 0.86/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | ? [X5] : (~v5_pre_topc(k4_waybel_1(X0,X5),X0,X0) & m1_subset_1(X5,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.86/1.03    inference(rectify,[],[f41])).
% 0.86/1.03  
% 0.86/1.03  fof(f58,plain,(
% 0.86/1.03    ! [X0] : (? [X5] : (~v5_pre_topc(k4_waybel_1(X0,X5),X0,X0) & m1_subset_1(X5,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 0.86/1.03    introduced(choice_axiom,[])).
% 0.86/1.03  
% 0.86/1.03  fof(f59,plain,(
% 0.86/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | (~v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0) & m1_subset_1(sK4(X0),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.86/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f57,f58])).
% 0.86/1.03  
% 0.86/1.03  fof(f87,plain,(
% 0.86/1.03    ( ! [X4,X2,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | m1_subset_1(sK4(X0),u1_struct_0(X0)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.86/1.03    inference(cnf_transformation,[],[f59])).
% 0.86/1.03  
% 0.86/1.03  fof(f112,plain,(
% 0.86/1.03    ( ! [X4,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | m1_subset_1(sK4(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.86/1.03    inference(equality_resolution,[],[f87])).
% 0.86/1.03  
% 0.86/1.03  fof(f96,plain,(
% 0.86/1.03    v1_compts_1(sK5)),
% 0.86/1.03    inference(cnf_transformation,[],[f63])).
% 0.86/1.03  
% 0.86/1.03  fof(f89,plain,(
% 0.86/1.03    v2_pre_topc(sK5)),
% 0.86/1.03    inference(cnf_transformation,[],[f63])).
% 0.86/1.03  
% 0.86/1.03  fof(f90,plain,(
% 0.86/1.03    v8_pre_topc(sK5)),
% 0.86/1.03    inference(cnf_transformation,[],[f63])).
% 0.86/1.03  
% 0.86/1.03  fof(f92,plain,(
% 0.86/1.03    v4_orders_2(sK5)),
% 0.86/1.03    inference(cnf_transformation,[],[f63])).
% 0.86/1.03  
% 0.86/1.03  fof(f93,plain,(
% 0.86/1.03    v5_orders_2(sK5)),
% 0.86/1.03    inference(cnf_transformation,[],[f63])).
% 0.86/1.03  
% 0.86/1.03  fof(f95,plain,(
% 0.86/1.03    v2_lattice3(sK5)),
% 0.86/1.03    inference(cnf_transformation,[],[f63])).
% 0.86/1.03  
% 0.86/1.03  fof(f99,plain,(
% 0.86/1.03    ~v2_struct_0(sK7)),
% 0.86/1.03    inference(cnf_transformation,[],[f63])).
% 0.86/1.03  
% 0.86/1.03  fof(f100,plain,(
% 0.86/1.03    v4_orders_2(sK7)),
% 0.86/1.03    inference(cnf_transformation,[],[f63])).
% 0.86/1.03  
% 0.86/1.03  fof(f102,plain,(
% 0.86/1.03    l1_waybel_0(sK7,sK5)),
% 0.86/1.03    inference(cnf_transformation,[],[f63])).
% 0.86/1.03  
% 0.86/1.03  fof(f98,plain,(
% 0.86/1.03    m1_subset_1(sK6,u1_struct_0(sK5))),
% 0.86/1.03    inference(cnf_transformation,[],[f63])).
% 0.86/1.03  
% 0.86/1.03  fof(f88,plain,(
% 0.86/1.03    ( ! [X4,X2,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | ~v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.86/1.03    inference(cnf_transformation,[],[f59])).
% 0.86/1.03  
% 0.86/1.03  fof(f111,plain,(
% 0.86/1.03    ( ! [X4,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | ~v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.86/1.03    inference(equality_resolution,[],[f88])).
% 0.86/1.03  
% 0.86/1.03  fof(f103,plain,(
% 0.86/1.03    ( ! [X3] : (v5_pre_topc(k4_waybel_1(sK5,X3),sK5,sK5) | ~m1_subset_1(X3,u1_struct_0(sK5))) )),
% 0.86/1.03    inference(cnf_transformation,[],[f63])).
% 0.86/1.03  
% 0.86/1.03  fof(f8,axiom,(
% 0.86/1.03    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 0.86/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.86/1.03  
% 0.86/1.03  fof(f18,plain,(
% 0.86/1.03    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 0.86/1.03    inference(pure_predicate_removal,[],[f8])).
% 0.86/1.03  
% 0.86/1.03  fof(f19,plain,(
% 0.86/1.03    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))))),
% 0.86/1.03    inference(pure_predicate_removal,[],[f18])).
% 0.86/1.03  
% 0.86/1.03  fof(f31,plain,(
% 0.86/1.03    ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 0.86/1.03    inference(ennf_transformation,[],[f19])).
% 0.86/1.03  
% 0.86/1.03  fof(f32,plain,(
% 0.86/1.03    ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 0.86/1.03    inference(flattening,[],[f31])).
% 0.86/1.03  
% 0.86/1.03  fof(f81,plain,(
% 0.86/1.03    ( ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.86/1.03    inference(cnf_transformation,[],[f32])).
% 0.86/1.03  
% 0.86/1.03  fof(f3,axiom,(
% 0.86/1.03    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.86/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.86/1.03  
% 0.86/1.03  fof(f22,plain,(
% 0.86/1.03    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.86/1.03    inference(ennf_transformation,[],[f3])).
% 0.86/1.03  
% 0.86/1.03  fof(f66,plain,(
% 0.86/1.03    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.86/1.03    inference(cnf_transformation,[],[f22])).
% 0.86/1.03  
% 0.86/1.03  fof(f2,axiom,(
% 0.86/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.86/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.86/1.03  
% 0.86/1.03  fof(f21,plain,(
% 0.86/1.03    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.86/1.03    inference(ennf_transformation,[],[f2])).
% 0.86/1.03  
% 0.86/1.03  fof(f65,plain,(
% 0.86/1.03    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.86/1.03    inference(cnf_transformation,[],[f21])).
% 0.86/1.03  
% 0.86/1.03  fof(f1,axiom,(
% 0.86/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.86/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.86/1.03  
% 0.86/1.03  fof(f20,plain,(
% 0.86/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.86/1.03    inference(ennf_transformation,[],[f1])).
% 0.86/1.03  
% 0.86/1.03  fof(f64,plain,(
% 0.86/1.03    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.86/1.03    inference(cnf_transformation,[],[f20])).
% 0.86/1.03  
% 0.86/1.03  fof(f10,axiom,(
% 0.86/1.03    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (v1_relat_1(X1) => k1_yellow_0(X0,k2_relat_1(X1)) = k4_yellow_2(X0,X1)))),
% 0.86/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.86/1.03  
% 0.86/1.03  fof(f35,plain,(
% 0.86/1.03    ! [X0] : (! [X1] : (k1_yellow_0(X0,k2_relat_1(X1)) = k4_yellow_2(X0,X1) | ~v1_relat_1(X1)) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.86/1.03    inference(ennf_transformation,[],[f10])).
% 0.86/1.03  
% 0.86/1.03  fof(f36,plain,(
% 0.86/1.03    ! [X0] : (! [X1] : (k1_yellow_0(X0,k2_relat_1(X1)) = k4_yellow_2(X0,X1) | ~v1_relat_1(X1)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.86/1.03    inference(flattening,[],[f35])).
% 0.86/1.03  
% 0.86/1.03  fof(f83,plain,(
% 0.86/1.03    ( ! [X0,X1] : (k1_yellow_0(X0,k2_relat_1(X1)) = k4_yellow_2(X0,X1) | ~v1_relat_1(X1) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.86/1.03    inference(cnf_transformation,[],[f36])).
% 0.86/1.03  
% 0.86/1.03  fof(f9,axiom,(
% 0.86/1.03    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (l1_waybel_0(X1,X0) => k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1))))),
% 0.86/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.86/1.03  
% 0.86/1.03  fof(f33,plain,(
% 0.86/1.03    ! [X0] : (! [X1] : (k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0)) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.86/1.03    inference(ennf_transformation,[],[f9])).
% 0.86/1.03  
% 0.86/1.03  fof(f34,plain,(
% 0.86/1.03    ! [X0] : (! [X1] : (k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.86/1.03    inference(flattening,[],[f33])).
% 0.86/1.03  
% 0.86/1.03  fof(f82,plain,(
% 0.86/1.03    ( ! [X0,X1] : (k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.86/1.03    inference(cnf_transformation,[],[f34])).
% 0.86/1.03  
% 0.86/1.03  fof(f12,axiom,(
% 0.86/1.03    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & v10_waybel_0(X1,X0) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3))))))),
% 0.86/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.86/1.03  
% 0.86/1.03  fof(f38,plain,(
% 0.86/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | (~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.86/1.03    inference(ennf_transformation,[],[f12])).
% 0.86/1.03  
% 0.86/1.03  fof(f39,plain,(
% 0.86/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.86/1.03    inference(flattening,[],[f38])).
% 0.86/1.03  
% 0.86/1.03  fof(f55,plain,(
% 0.86/1.03    ! [X0] : (? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 0.86/1.03    introduced(choice_axiom,[])).
% 0.86/1.03  
% 0.86/1.03  fof(f56,plain,(
% 0.86/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | (~v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0) & m1_subset_1(sK3(X0),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.86/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f55])).
% 0.86/1.03  
% 0.86/1.03  fof(f86,plain,(
% 0.86/1.03    ( ! [X2,X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.86/1.03    inference(cnf_transformation,[],[f56])).
% 0.86/1.03  
% 0.86/1.03  fof(f109,plain,(
% 0.86/1.03    ( ! [X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v10_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.86/1.03    inference(equality_resolution,[],[f86])).
% 0.86/1.03  
% 0.86/1.03  fof(f104,plain,(
% 0.86/1.03    v10_waybel_0(sK7,sK5)),
% 0.86/1.03    inference(cnf_transformation,[],[f63])).
% 0.86/1.03  
% 0.86/1.03  fof(f85,plain,(
% 0.86/1.03    ( ! [X2,X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | m1_subset_1(sK3(X0),u1_struct_0(X0)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.86/1.03    inference(cnf_transformation,[],[f56])).
% 0.86/1.03  
% 0.86/1.03  fof(f110,plain,(
% 0.86/1.03    ( ! [X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v10_waybel_0(X1,X0) | m1_subset_1(sK3(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.86/1.03    inference(equality_resolution,[],[f85])).
% 0.86/1.03  
% 0.86/1.03  fof(f7,axiom,(
% 0.86/1.03    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (r1_yellow_0(X0,X1) <=> ? [X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 0.86/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.86/1.03  
% 0.86/1.03  fof(f29,plain,(
% 0.86/1.03    ! [X0] : (! [X1] : (r1_yellow_0(X0,X1) <=> ? [X2] : (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.86/1.03    inference(ennf_transformation,[],[f7])).
% 0.86/1.03  
% 0.86/1.03  fof(f30,plain,(
% 0.86/1.03    ! [X0] : (! [X1] : (r1_yellow_0(X0,X1) <=> ? [X2] : (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.86/1.03    inference(flattening,[],[f29])).
% 0.86/1.03  
% 0.86/1.03  fof(f50,plain,(
% 0.86/1.03    ! [X0] : (! [X1] : ((r1_yellow_0(X0,X1) | ! [X2] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (? [X2] : (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r1_yellow_0(X0,X1))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.86/1.03    inference(nnf_transformation,[],[f30])).
% 0.86/1.03  
% 0.86/1.03  fof(f51,plain,(
% 0.86/1.03    ! [X0] : (! [X1] : ((r1_yellow_0(X0,X1) | ! [X2] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (? [X4] : (! [X5] : (r1_orders_2(X0,X4,X5) | ~r2_lattice3(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r2_lattice3(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_yellow_0(X0,X1))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.86/1.03    inference(rectify,[],[f50])).
% 0.86/1.03  
% 0.86/1.03  fof(f53,plain,(
% 0.86/1.03    ! [X1,X0] : (? [X4] : (! [X5] : (r1_orders_2(X0,X4,X5) | ~r2_lattice3(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r2_lattice3(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (! [X5] : (r1_orders_2(X0,sK2(X0,X1),X5) | ~r2_lattice3(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r2_lattice3(X0,X1,sK2(X0,X1)) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 0.86/1.03    introduced(choice_axiom,[])).
% 0.86/1.03  
% 0.86/1.03  fof(f52,plain,(
% 0.86/1.03    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK1(X0,X1,X2)) & r2_lattice3(X0,X1,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 0.86/1.03    introduced(choice_axiom,[])).
% 0.86/1.03  
% 0.86/1.03  fof(f54,plain,(
% 0.86/1.03    ! [X0] : (! [X1] : ((r1_yellow_0(X0,X1) | ! [X2] : ((~r1_orders_2(X0,X2,sK1(X0,X1,X2)) & r2_lattice3(X0,X1,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)))) & ((! [X5] : (r1_orders_2(X0,sK2(X0,X1),X5) | ~r2_lattice3(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r2_lattice3(X0,X1,sK2(X0,X1)) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) | ~r1_yellow_0(X0,X1))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.86/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f51,f53,f52])).
% 0.86/1.03  
% 0.86/1.03  fof(f79,plain,(
% 0.86/1.03    ( ! [X2,X0,X1] : (r1_yellow_0(X0,X1) | r2_lattice3(X0,X1,sK1(X0,X1,X2)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.86/1.03    inference(cnf_transformation,[],[f54])).
% 0.86/1.03  
% 0.86/1.03  fof(f78,plain,(
% 0.86/1.03    ( ! [X2,X0,X1] : (r1_yellow_0(X0,X1) | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.86/1.03    inference(cnf_transformation,[],[f54])).
% 0.86/1.03  
% 0.86/1.03  fof(f80,plain,(
% 0.86/1.03    ( ! [X2,X0,X1] : (r1_yellow_0(X0,X1) | ~r1_orders_2(X0,X2,sK1(X0,X1,X2)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.86/1.03    inference(cnf_transformation,[],[f54])).
% 0.86/1.03  
% 0.86/1.03  fof(f74,plain,(
% 0.86/1.03    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X1) = X2 | ~r1_orders_2(X0,X2,sK0(X0,X1,X2)) | ~r2_lattice3(X0,X1,X2) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.86/1.03    inference(cnf_transformation,[],[f49])).
% 0.86/1.03  
% 0.86/1.03  fof(f106,plain,(
% 0.86/1.03    k1_waybel_2(sK5,sK7) != sK6),
% 0.86/1.03    inference(cnf_transformation,[],[f63])).
% 0.86/1.03  
% 0.86/1.03  cnf(c_8,plain,
% 0.86/1.03      ( ~ r2_lattice3(X0,X1,X2)
% 0.86/1.03      | ~ r1_yellow_0(X0,X1)
% 0.86/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.86/1.03      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 0.86/1.03      | ~ l1_orders_2(X0)
% 0.86/1.03      | k1_yellow_0(X0,X1) = X2 ),
% 0.86/1.03      inference(cnf_transformation,[],[f72]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_20,plain,
% 0.86/1.03      ( ~ l1_waybel_9(X0) | l1_orders_2(X0) ),
% 0.86/1.03      inference(cnf_transformation,[],[f84]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_34,negated_conjecture,
% 0.86/1.03      ( l1_waybel_9(sK5) ),
% 0.86/1.03      inference(cnf_transformation,[],[f97]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_693,plain,
% 0.86/1.03      ( l1_orders_2(X0) | sK5 != X0 ),
% 0.86/1.03      inference(resolution_lifted,[status(thm)],[c_20,c_34]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_694,plain,
% 0.86/1.03      ( l1_orders_2(sK5) ),
% 0.86/1.03      inference(unflattening,[status(thm)],[c_693]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_1304,plain,
% 0.86/1.03      ( ~ r2_lattice3(X0,X1,X2)
% 0.86/1.03      | ~ r1_yellow_0(X0,X1)
% 0.86/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.86/1.03      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 0.86/1.03      | k1_yellow_0(X0,X1) = X2
% 0.86/1.03      | sK5 != X0 ),
% 0.86/1.03      inference(resolution_lifted,[status(thm)],[c_8,c_694]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_1305,plain,
% 0.86/1.03      ( ~ r2_lattice3(sK5,X0,X1)
% 0.86/1.03      | ~ r1_yellow_0(sK5,X0)
% 0.86/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 0.86/1.03      | m1_subset_1(sK0(sK5,X0,X1),u1_struct_0(sK5))
% 0.86/1.03      | k1_yellow_0(sK5,X0) = X1 ),
% 0.86/1.03      inference(unflattening,[status(thm)],[c_1304]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_3461,plain,
% 0.86/1.03      ( ~ r2_lattice3(sK5,X0_71,X0_69)
% 0.86/1.03      | ~ r1_yellow_0(sK5,X0_71)
% 0.86/1.03      | ~ m1_subset_1(X0_69,u1_struct_0(sK5))
% 0.86/1.03      | m1_subset_1(sK0(sK5,X0_71,X0_69),u1_struct_0(sK5))
% 0.86/1.03      | k1_yellow_0(sK5,X0_71) = X0_69 ),
% 0.86/1.03      inference(subtyping,[status(esa)],[c_1305]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_3983,plain,
% 0.86/1.03      ( k1_yellow_0(sK5,X0_71) = X0_69
% 0.86/1.03      | r2_lattice3(sK5,X0_71,X0_69) != iProver_top
% 0.86/1.03      | r1_yellow_0(sK5,X0_71) != iProver_top
% 0.86/1.03      | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top
% 0.86/1.03      | m1_subset_1(sK0(sK5,X0_71,X0_69),u1_struct_0(sK5)) = iProver_top ),
% 0.86/1.03      inference(predicate_to_equality,[status(thm)],[c_3461]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_7,plain,
% 0.86/1.03      ( ~ r2_lattice3(X0,X1,X2)
% 0.86/1.03      | r2_lattice3(X0,X1,sK0(X0,X1,X2))
% 0.86/1.03      | ~ r1_yellow_0(X0,X1)
% 0.86/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.86/1.03      | ~ l1_orders_2(X0)
% 0.86/1.03      | k1_yellow_0(X0,X1) = X2 ),
% 0.86/1.03      inference(cnf_transformation,[],[f73]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_1325,plain,
% 0.86/1.03      ( ~ r2_lattice3(X0,X1,X2)
% 0.86/1.03      | r2_lattice3(X0,X1,sK0(X0,X1,X2))
% 0.86/1.03      | ~ r1_yellow_0(X0,X1)
% 0.86/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.86/1.03      | k1_yellow_0(X0,X1) = X2
% 0.86/1.03      | sK5 != X0 ),
% 0.86/1.03      inference(resolution_lifted,[status(thm)],[c_7,c_694]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_1326,plain,
% 0.86/1.03      ( ~ r2_lattice3(sK5,X0,X1)
% 0.86/1.03      | r2_lattice3(sK5,X0,sK0(sK5,X0,X1))
% 0.86/1.03      | ~ r1_yellow_0(sK5,X0)
% 0.86/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 0.86/1.03      | k1_yellow_0(sK5,X0) = X1 ),
% 0.86/1.03      inference(unflattening,[status(thm)],[c_1325]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_3460,plain,
% 0.86/1.03      ( ~ r2_lattice3(sK5,X0_71,X0_69)
% 0.86/1.03      | r2_lattice3(sK5,X0_71,sK0(sK5,X0_71,X0_69))
% 0.86/1.03      | ~ r1_yellow_0(sK5,X0_71)
% 0.86/1.03      | ~ m1_subset_1(X0_69,u1_struct_0(sK5))
% 0.86/1.03      | k1_yellow_0(sK5,X0_71) = X0_69 ),
% 0.86/1.03      inference(subtyping,[status(esa)],[c_1326]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_3984,plain,
% 0.86/1.03      ( k1_yellow_0(sK5,X0_71) = X0_69
% 0.86/1.03      | r2_lattice3(sK5,X0_71,X0_69) != iProver_top
% 0.86/1.03      | r2_lattice3(sK5,X0_71,sK0(sK5,X0_71,X0_69)) = iProver_top
% 0.86/1.03      | r1_yellow_0(sK5,X0_71) != iProver_top
% 0.86/1.03      | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top ),
% 0.86/1.03      inference(predicate_to_equality,[status(thm)],[c_3460]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_4,plain,
% 0.86/1.03      ( r1_orders_2(X0,X1,X2)
% 0.86/1.03      | ~ r3_orders_2(X0,X1,X2)
% 0.86/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.86/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 0.86/1.03      | v2_struct_0(X0)
% 0.86/1.03      | ~ v3_orders_2(X0)
% 0.86/1.03      | ~ l1_orders_2(X0) ),
% 0.86/1.03      inference(cnf_transformation,[],[f67]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_40,negated_conjecture,
% 0.86/1.03      ( v3_orders_2(sK5) ),
% 0.86/1.03      inference(cnf_transformation,[],[f91]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_715,plain,
% 0.86/1.03      ( r1_orders_2(X0,X1,X2)
% 0.86/1.03      | ~ r3_orders_2(X0,X1,X2)
% 0.86/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.86/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 0.86/1.03      | v2_struct_0(X0)
% 0.86/1.03      | ~ l1_orders_2(X0)
% 0.86/1.03      | sK5 != X0 ),
% 0.86/1.03      inference(resolution_lifted,[status(thm)],[c_4,c_40]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_716,plain,
% 0.86/1.03      ( r1_orders_2(sK5,X0,X1)
% 0.86/1.03      | ~ r3_orders_2(sK5,X0,X1)
% 0.86/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 0.86/1.03      | v2_struct_0(sK5)
% 0.86/1.03      | ~ l1_orders_2(sK5) ),
% 0.86/1.03      inference(unflattening,[status(thm)],[c_715]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_37,negated_conjecture,
% 0.86/1.03      ( v1_lattice3(sK5) ),
% 0.86/1.03      inference(cnf_transformation,[],[f94]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_75,plain,
% 0.86/1.03      ( ~ l1_waybel_9(sK5) | l1_orders_2(sK5) ),
% 0.86/1.03      inference(instantiation,[status(thm)],[c_20]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_5,plain,
% 0.86/1.03      ( ~ v1_lattice3(X0) | ~ v2_struct_0(X0) | ~ l1_orders_2(X0) ),
% 0.86/1.03      inference(cnf_transformation,[],[f69]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_120,plain,
% 0.86/1.03      ( ~ v1_lattice3(sK5) | ~ v2_struct_0(sK5) | ~ l1_orders_2(sK5) ),
% 0.86/1.03      inference(instantiation,[status(thm)],[c_5]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_720,plain,
% 0.86/1.03      ( r1_orders_2(sK5,X0,X1)
% 0.86/1.03      | ~ r3_orders_2(sK5,X0,X1)
% 0.86/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 0.86/1.03      inference(global_propositional_subsumption,
% 0.86/1.03                [status(thm)],
% 0.86/1.03                [c_716,c_37,c_34,c_75,c_120]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_721,plain,
% 0.86/1.03      ( r1_orders_2(sK5,X0,X1)
% 0.86/1.03      | ~ r3_orders_2(sK5,X0,X1)
% 0.86/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
% 0.86/1.03      inference(renaming,[status(thm)],[c_720]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_26,negated_conjecture,
% 0.86/1.03      ( r3_waybel_9(sK5,sK7,sK6) ),
% 0.86/1.03      inference(cnf_transformation,[],[f105]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_30,negated_conjecture,
% 0.86/1.03      ( v7_waybel_0(sK7) ),
% 0.86/1.03      inference(cnf_transformation,[],[f101]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_24,plain,
% 0.86/1.03      ( ~ r3_waybel_9(X0,X1,X2)
% 0.86/1.03      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 0.86/1.03      | r3_orders_2(X0,X2,X3)
% 0.86/1.03      | ~ l1_waybel_0(X1,X0)
% 0.86/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 0.86/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.86/1.03      | m1_subset_1(sK4(X0),u1_struct_0(X0))
% 0.86/1.03      | ~ v2_pre_topc(X0)
% 0.86/1.03      | ~ v8_pre_topc(X0)
% 0.86/1.03      | ~ v2_lattice3(X0)
% 0.86/1.03      | ~ v1_compts_1(X0)
% 0.86/1.03      | ~ v4_orders_2(X1)
% 0.86/1.03      | ~ v4_orders_2(X0)
% 0.86/1.03      | ~ v7_waybel_0(X1)
% 0.86/1.03      | ~ l1_waybel_9(X0)
% 0.86/1.03      | ~ v5_orders_2(X0)
% 0.86/1.03      | ~ v1_lattice3(X0)
% 0.86/1.03      | v2_struct_0(X1)
% 0.86/1.03      | ~ v3_orders_2(X0) ),
% 0.86/1.03      inference(cnf_transformation,[],[f112]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_35,negated_conjecture,
% 0.86/1.03      ( v1_compts_1(sK5) ),
% 0.86/1.03      inference(cnf_transformation,[],[f96]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_640,plain,
% 0.86/1.03      ( ~ r3_waybel_9(X0,X1,X2)
% 0.86/1.03      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 0.86/1.03      | r3_orders_2(X0,X2,X3)
% 0.86/1.03      | ~ l1_waybel_0(X1,X0)
% 0.86/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.86/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 0.86/1.03      | m1_subset_1(sK4(X0),u1_struct_0(X0))
% 0.86/1.03      | ~ v2_pre_topc(X0)
% 0.86/1.03      | ~ v8_pre_topc(X0)
% 0.86/1.03      | ~ v2_lattice3(X0)
% 0.86/1.03      | ~ v4_orders_2(X1)
% 0.86/1.03      | ~ v4_orders_2(X0)
% 0.86/1.03      | ~ v7_waybel_0(X1)
% 0.86/1.03      | ~ l1_waybel_9(X0)
% 0.86/1.03      | ~ v5_orders_2(X0)
% 0.86/1.03      | ~ v1_lattice3(X0)
% 0.86/1.03      | v2_struct_0(X1)
% 0.86/1.03      | ~ v3_orders_2(X0)
% 0.86/1.03      | sK5 != X0 ),
% 0.86/1.03      inference(resolution_lifted,[status(thm)],[c_24,c_35]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_641,plain,
% 0.86/1.03      ( ~ r3_waybel_9(sK5,X0,X1)
% 0.86/1.03      | ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK5),u1_waybel_0(sK5,X0)),X2)
% 0.86/1.03      | r3_orders_2(sK5,X1,X2)
% 0.86/1.03      | ~ l1_waybel_0(X0,sK5)
% 0.86/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 0.86/1.03      | m1_subset_1(sK4(sK5),u1_struct_0(sK5))
% 0.86/1.03      | ~ v2_pre_topc(sK5)
% 0.86/1.03      | ~ v8_pre_topc(sK5)
% 0.86/1.03      | ~ v2_lattice3(sK5)
% 0.86/1.03      | ~ v4_orders_2(X0)
% 0.86/1.03      | ~ v4_orders_2(sK5)
% 0.86/1.03      | ~ v7_waybel_0(X0)
% 0.86/1.03      | ~ l1_waybel_9(sK5)
% 0.86/1.03      | ~ v5_orders_2(sK5)
% 0.86/1.03      | ~ v1_lattice3(sK5)
% 0.86/1.03      | v2_struct_0(X0)
% 0.86/1.03      | ~ v3_orders_2(sK5) ),
% 0.86/1.03      inference(unflattening,[status(thm)],[c_640]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_42,negated_conjecture,
% 0.86/1.03      ( v2_pre_topc(sK5) ),
% 0.86/1.03      inference(cnf_transformation,[],[f89]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_41,negated_conjecture,
% 0.86/1.03      ( v8_pre_topc(sK5) ),
% 0.86/1.03      inference(cnf_transformation,[],[f90]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_39,negated_conjecture,
% 0.86/1.03      ( v4_orders_2(sK5) ),
% 0.86/1.03      inference(cnf_transformation,[],[f92]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_38,negated_conjecture,
% 0.86/1.03      ( v5_orders_2(sK5) ),
% 0.86/1.03      inference(cnf_transformation,[],[f93]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_36,negated_conjecture,
% 0.86/1.03      ( v2_lattice3(sK5) ),
% 0.86/1.03      inference(cnf_transformation,[],[f95]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_645,plain,
% 0.86/1.03      ( v2_struct_0(X0)
% 0.86/1.03      | ~ v4_orders_2(X0)
% 0.86/1.03      | ~ r3_waybel_9(sK5,X0,X1)
% 0.86/1.03      | ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK5),u1_waybel_0(sK5,X0)),X2)
% 0.86/1.03      | r3_orders_2(sK5,X1,X2)
% 0.86/1.03      | ~ l1_waybel_0(X0,sK5)
% 0.86/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 0.86/1.03      | m1_subset_1(sK4(sK5),u1_struct_0(sK5))
% 0.86/1.03      | ~ v7_waybel_0(X0) ),
% 0.86/1.03      inference(global_propositional_subsumption,
% 0.86/1.03                [status(thm)],
% 0.86/1.03                [c_641,c_42,c_41,c_40,c_39,c_38,c_37,c_36,c_34]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_646,plain,
% 0.86/1.03      ( ~ r3_waybel_9(sK5,X0,X1)
% 0.86/1.03      | ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK5),u1_waybel_0(sK5,X0)),X2)
% 0.86/1.03      | r3_orders_2(sK5,X1,X2)
% 0.86/1.03      | ~ l1_waybel_0(X0,sK5)
% 0.86/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 0.86/1.03      | m1_subset_1(sK4(sK5),u1_struct_0(sK5))
% 0.86/1.03      | ~ v4_orders_2(X0)
% 0.86/1.03      | ~ v7_waybel_0(X0)
% 0.86/1.03      | v2_struct_0(X0) ),
% 0.86/1.03      inference(renaming,[status(thm)],[c_645]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_773,plain,
% 0.86/1.03      ( ~ r3_waybel_9(sK5,X0,X1)
% 0.86/1.03      | ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK5),u1_waybel_0(sK5,X0)),X2)
% 0.86/1.03      | r3_orders_2(sK5,X1,X2)
% 0.86/1.03      | ~ l1_waybel_0(X0,sK5)
% 0.86/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 0.86/1.03      | m1_subset_1(sK4(sK5),u1_struct_0(sK5))
% 0.86/1.03      | ~ v4_orders_2(X0)
% 0.86/1.03      | v2_struct_0(X0)
% 0.86/1.03      | sK7 != X0 ),
% 0.86/1.03      inference(resolution_lifted,[status(thm)],[c_30,c_646]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_774,plain,
% 0.86/1.03      ( ~ r3_waybel_9(sK5,sK7,X0)
% 0.86/1.03      | ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X1)
% 0.86/1.03      | r3_orders_2(sK5,X0,X1)
% 0.86/1.03      | ~ l1_waybel_0(sK7,sK5)
% 0.86/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 0.86/1.03      | m1_subset_1(sK4(sK5),u1_struct_0(sK5))
% 0.86/1.03      | ~ v4_orders_2(sK7)
% 0.86/1.03      | v2_struct_0(sK7) ),
% 0.86/1.03      inference(unflattening,[status(thm)],[c_773]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_32,negated_conjecture,
% 0.86/1.03      ( ~ v2_struct_0(sK7) ),
% 0.86/1.03      inference(cnf_transformation,[],[f99]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_31,negated_conjecture,
% 0.86/1.03      ( v4_orders_2(sK7) ),
% 0.86/1.03      inference(cnf_transformation,[],[f100]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_29,negated_conjecture,
% 0.86/1.03      ( l1_waybel_0(sK7,sK5) ),
% 0.86/1.03      inference(cnf_transformation,[],[f102]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_778,plain,
% 0.86/1.03      ( r3_orders_2(sK5,X0,X1)
% 0.86/1.03      | ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X1)
% 0.86/1.03      | ~ r3_waybel_9(sK5,sK7,X0)
% 0.86/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 0.86/1.03      | m1_subset_1(sK4(sK5),u1_struct_0(sK5)) ),
% 0.86/1.03      inference(global_propositional_subsumption,
% 0.86/1.03                [status(thm)],
% 0.86/1.03                [c_774,c_32,c_31,c_29]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_779,plain,
% 0.86/1.03      ( ~ r3_waybel_9(sK5,sK7,X0)
% 0.86/1.03      | ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X1)
% 0.86/1.03      | r3_orders_2(sK5,X0,X1)
% 0.86/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 0.86/1.03      | m1_subset_1(sK4(sK5),u1_struct_0(sK5)) ),
% 0.86/1.03      inference(renaming,[status(thm)],[c_778]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_970,plain,
% 0.86/1.03      ( ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
% 0.86/1.03      | r3_orders_2(sK5,X1,X0)
% 0.86/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 0.86/1.03      | m1_subset_1(sK4(sK5),u1_struct_0(sK5))
% 0.86/1.03      | sK6 != X1
% 0.86/1.03      | sK7 != sK7
% 0.86/1.03      | sK5 != sK5 ),
% 0.86/1.03      inference(resolution_lifted,[status(thm)],[c_26,c_779]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_971,plain,
% 0.86/1.03      ( ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
% 0.86/1.03      | r3_orders_2(sK5,sK6,X0)
% 0.86/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 0.86/1.03      | m1_subset_1(sK4(sK5),u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 0.86/1.03      inference(unflattening,[status(thm)],[c_970]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_33,negated_conjecture,
% 0.86/1.03      ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 0.86/1.03      inference(cnf_transformation,[],[f98]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_975,plain,
% 0.86/1.03      ( m1_subset_1(sK4(sK5),u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 0.86/1.03      | r3_orders_2(sK5,sK6,X0)
% 0.86/1.03      | ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0) ),
% 0.86/1.03      inference(global_propositional_subsumption,
% 0.86/1.03                [status(thm)],
% 0.86/1.03                [c_971,c_33]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_976,plain,
% 0.86/1.03      ( ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
% 0.86/1.03      | r3_orders_2(sK5,sK6,X0)
% 0.86/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 0.86/1.03      | m1_subset_1(sK4(sK5),u1_struct_0(sK5)) ),
% 0.86/1.03      inference(renaming,[status(thm)],[c_975]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_1048,plain,
% 0.86/1.03      ( ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
% 0.86/1.03      | r1_orders_2(sK5,X1,X2)
% 0.86/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 0.86/1.03      | m1_subset_1(sK4(sK5),u1_struct_0(sK5))
% 0.86/1.03      | X0 != X2
% 0.86/1.03      | sK6 != X1
% 0.86/1.03      | sK5 != sK5 ),
% 0.86/1.03      inference(resolution_lifted,[status(thm)],[c_721,c_976]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_1049,plain,
% 0.86/1.03      ( ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
% 0.86/1.03      | r1_orders_2(sK5,sK6,X0)
% 0.86/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 0.86/1.03      | m1_subset_1(sK4(sK5),u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 0.86/1.03      inference(unflattening,[status(thm)],[c_1048]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_1053,plain,
% 0.86/1.03      ( m1_subset_1(sK4(sK5),u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 0.86/1.03      | r1_orders_2(sK5,sK6,X0)
% 0.86/1.03      | ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0) ),
% 0.86/1.03      inference(global_propositional_subsumption,
% 0.86/1.03                [status(thm)],
% 0.86/1.03                [c_1049,c_33]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_1054,plain,
% 0.86/1.03      ( ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
% 0.86/1.03      | r1_orders_2(sK5,sK6,X0)
% 0.86/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 0.86/1.03      | m1_subset_1(sK4(sK5),u1_struct_0(sK5)) ),
% 0.86/1.03      inference(renaming,[status(thm)],[c_1053]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_3471,plain,
% 0.86/1.03      ( ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0_69)
% 0.86/1.03      | r1_orders_2(sK5,sK6,X0_69)
% 0.86/1.03      | ~ m1_subset_1(X0_69,u1_struct_0(sK5))
% 0.86/1.03      | m1_subset_1(sK4(sK5),u1_struct_0(sK5)) ),
% 0.86/1.03      inference(subtyping,[status(esa)],[c_1054]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_3971,plain,
% 0.86/1.03      ( r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0_69) != iProver_top
% 0.86/1.03      | r1_orders_2(sK5,sK6,X0_69) = iProver_top
% 0.86/1.03      | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top
% 0.86/1.03      | m1_subset_1(sK4(sK5),u1_struct_0(sK5)) = iProver_top ),
% 0.86/1.03      inference(predicate_to_equality,[status(thm)],[c_3471]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_3553,plain,
% 0.86/1.03      ( r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0_69) != iProver_top
% 0.86/1.03      | r1_orders_2(sK5,sK6,X0_69) = iProver_top
% 0.86/1.03      | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top
% 0.86/1.03      | m1_subset_1(sK4(sK5),u1_struct_0(sK5)) = iProver_top ),
% 0.86/1.03      inference(predicate_to_equality,[status(thm)],[c_3471]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_23,plain,
% 0.86/1.03      ( ~ v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0)
% 0.86/1.03      | ~ r3_waybel_9(X0,X1,X2)
% 0.86/1.03      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 0.86/1.03      | r3_orders_2(X0,X2,X3)
% 0.86/1.03      | ~ l1_waybel_0(X1,X0)
% 0.86/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 0.86/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.86/1.03      | ~ v2_pre_topc(X0)
% 0.86/1.03      | ~ v8_pre_topc(X0)
% 0.86/1.03      | ~ v2_lattice3(X0)
% 0.86/1.03      | ~ v1_compts_1(X0)
% 0.86/1.03      | ~ v4_orders_2(X1)
% 0.86/1.03      | ~ v4_orders_2(X0)
% 0.86/1.03      | ~ v7_waybel_0(X1)
% 0.86/1.03      | ~ l1_waybel_9(X0)
% 0.86/1.03      | ~ v5_orders_2(X0)
% 0.86/1.03      | ~ v1_lattice3(X0)
% 0.86/1.03      | v2_struct_0(X1)
% 0.86/1.03      | ~ v3_orders_2(X0) ),
% 0.86/1.03      inference(cnf_transformation,[],[f111]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_28,negated_conjecture,
% 0.86/1.03      ( v5_pre_topc(k4_waybel_1(sK5,X0),sK5,sK5)
% 0.86/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 0.86/1.03      inference(cnf_transformation,[],[f103]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_564,plain,
% 0.86/1.03      ( ~ r3_waybel_9(X0,X1,X2)
% 0.86/1.03      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 0.86/1.03      | r3_orders_2(X0,X2,X3)
% 0.86/1.03      | ~ l1_waybel_0(X1,X0)
% 0.86/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.86/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 0.86/1.03      | ~ m1_subset_1(X4,u1_struct_0(sK5))
% 0.86/1.03      | ~ v2_pre_topc(X0)
% 0.86/1.03      | ~ v8_pre_topc(X0)
% 0.86/1.03      | ~ v2_lattice3(X0)
% 0.86/1.03      | ~ v1_compts_1(X0)
% 0.86/1.03      | ~ v4_orders_2(X1)
% 0.86/1.03      | ~ v4_orders_2(X0)
% 0.86/1.03      | ~ v7_waybel_0(X1)
% 0.86/1.03      | ~ l1_waybel_9(X0)
% 0.86/1.03      | ~ v5_orders_2(X0)
% 0.86/1.03      | ~ v1_lattice3(X0)
% 0.86/1.03      | v2_struct_0(X1)
% 0.86/1.03      | ~ v3_orders_2(X0)
% 0.86/1.03      | k4_waybel_1(X0,sK4(X0)) != k4_waybel_1(sK5,X4)
% 0.86/1.03      | sK5 != X0 ),
% 0.86/1.03      inference(resolution_lifted,[status(thm)],[c_23,c_28]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_565,plain,
% 0.86/1.03      ( ~ r3_waybel_9(sK5,X0,X1)
% 0.86/1.03      | ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK5),u1_waybel_0(sK5,X0)),X2)
% 0.86/1.03      | r3_orders_2(sK5,X1,X2)
% 0.86/1.03      | ~ l1_waybel_0(X0,sK5)
% 0.86/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X3,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 0.86/1.03      | ~ v2_pre_topc(sK5)
% 0.86/1.03      | ~ v8_pre_topc(sK5)
% 0.86/1.03      | ~ v2_lattice3(sK5)
% 0.86/1.03      | ~ v1_compts_1(sK5)
% 0.86/1.03      | ~ v4_orders_2(X0)
% 0.86/1.03      | ~ v4_orders_2(sK5)
% 0.86/1.03      | ~ v7_waybel_0(X0)
% 0.86/1.03      | ~ l1_waybel_9(sK5)
% 0.86/1.03      | ~ v5_orders_2(sK5)
% 0.86/1.03      | ~ v1_lattice3(sK5)
% 0.86/1.03      | v2_struct_0(X0)
% 0.86/1.03      | ~ v3_orders_2(sK5)
% 0.86/1.03      | k4_waybel_1(sK5,sK4(sK5)) != k4_waybel_1(sK5,X3) ),
% 0.86/1.03      inference(unflattening,[status(thm)],[c_564]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_569,plain,
% 0.86/1.03      ( v2_struct_0(X0)
% 0.86/1.03      | ~ v4_orders_2(X0)
% 0.86/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X3,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 0.86/1.03      | ~ l1_waybel_0(X0,sK5)
% 0.86/1.03      | r3_orders_2(sK5,X1,X2)
% 0.86/1.03      | ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK5),u1_waybel_0(sK5,X0)),X2)
% 0.86/1.03      | ~ r3_waybel_9(sK5,X0,X1)
% 0.86/1.03      | ~ v7_waybel_0(X0)
% 0.86/1.03      | k4_waybel_1(sK5,sK4(sK5)) != k4_waybel_1(sK5,X3) ),
% 0.86/1.03      inference(global_propositional_subsumption,
% 0.86/1.03                [status(thm)],
% 0.86/1.03                [c_565,c_42,c_41,c_40,c_39,c_38,c_37,c_36,c_35,c_34]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_570,plain,
% 0.86/1.03      ( ~ r3_waybel_9(sK5,X0,X1)
% 0.86/1.03      | ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK5),u1_waybel_0(sK5,X0)),X2)
% 0.86/1.03      | r3_orders_2(sK5,X1,X2)
% 0.86/1.03      | ~ l1_waybel_0(X0,sK5)
% 0.86/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X3,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 0.86/1.03      | ~ v4_orders_2(X0)
% 0.86/1.03      | ~ v7_waybel_0(X0)
% 0.86/1.03      | v2_struct_0(X0)
% 0.86/1.03      | k4_waybel_1(sK5,sK4(sK5)) != k4_waybel_1(sK5,X3) ),
% 0.86/1.03      inference(renaming,[status(thm)],[c_569]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_803,plain,
% 0.86/1.03      ( ~ r3_waybel_9(sK5,X0,X1)
% 0.86/1.03      | ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK5),u1_waybel_0(sK5,X0)),X2)
% 0.86/1.03      | r3_orders_2(sK5,X1,X2)
% 0.86/1.03      | ~ l1_waybel_0(X0,sK5)
% 0.86/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X3,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 0.86/1.03      | ~ v4_orders_2(X0)
% 0.86/1.03      | v2_struct_0(X0)
% 0.86/1.03      | k4_waybel_1(sK5,sK4(sK5)) != k4_waybel_1(sK5,X3)
% 0.86/1.03      | sK7 != X0 ),
% 0.86/1.03      inference(resolution_lifted,[status(thm)],[c_30,c_570]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_804,plain,
% 0.86/1.03      ( ~ r3_waybel_9(sK5,sK7,X0)
% 0.86/1.03      | ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X1)
% 0.86/1.03      | r3_orders_2(sK5,X0,X1)
% 0.86/1.03      | ~ l1_waybel_0(sK7,sK5)
% 0.86/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 0.86/1.03      | ~ v4_orders_2(sK7)
% 0.86/1.03      | v2_struct_0(sK7)
% 0.86/1.03      | k4_waybel_1(sK5,sK4(sK5)) != k4_waybel_1(sK5,X2) ),
% 0.86/1.03      inference(unflattening,[status(thm)],[c_803]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_808,plain,
% 0.86/1.03      ( r3_orders_2(sK5,X0,X1)
% 0.86/1.03      | ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X1)
% 0.86/1.03      | ~ r3_waybel_9(sK5,sK7,X0)
% 0.86/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 0.86/1.03      | k4_waybel_1(sK5,sK4(sK5)) != k4_waybel_1(sK5,X2) ),
% 0.86/1.03      inference(global_propositional_subsumption,
% 0.86/1.03                [status(thm)],
% 0.86/1.03                [c_804,c_32,c_31,c_29]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_809,plain,
% 0.86/1.03      ( ~ r3_waybel_9(sK5,sK7,X0)
% 0.86/1.03      | ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X1)
% 0.86/1.03      | r3_orders_2(sK5,X0,X1)
% 0.86/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 0.86/1.03      | k4_waybel_1(sK5,sK4(sK5)) != k4_waybel_1(sK5,X2) ),
% 0.86/1.03      inference(renaming,[status(thm)],[c_808]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_943,plain,
% 0.86/1.03      ( ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
% 0.86/1.03      | r3_orders_2(sK5,X1,X0)
% 0.86/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 0.86/1.03      | k4_waybel_1(sK5,sK4(sK5)) != k4_waybel_1(sK5,X2)
% 0.86/1.03      | sK6 != X1
% 0.86/1.03      | sK7 != sK7
% 0.86/1.03      | sK5 != sK5 ),
% 0.86/1.03      inference(resolution_lifted,[status(thm)],[c_26,c_809]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_944,plain,
% 0.86/1.03      ( ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
% 0.86/1.03      | r3_orders_2(sK5,sK6,X0)
% 0.86/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 0.86/1.03      | k4_waybel_1(sK5,sK4(sK5)) != k4_waybel_1(sK5,X1) ),
% 0.86/1.03      inference(unflattening,[status(thm)],[c_943]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_948,plain,
% 0.86/1.03      ( ~ m1_subset_1(X1,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 0.86/1.03      | r3_orders_2(sK5,sK6,X0)
% 0.86/1.03      | ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
% 0.86/1.03      | k4_waybel_1(sK5,sK4(sK5)) != k4_waybel_1(sK5,X1) ),
% 0.86/1.03      inference(global_propositional_subsumption,
% 0.86/1.03                [status(thm)],
% 0.86/1.03                [c_944,c_33]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_949,plain,
% 0.86/1.03      ( ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
% 0.86/1.03      | r3_orders_2(sK5,sK6,X0)
% 0.86/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 0.86/1.03      | k4_waybel_1(sK5,sK4(sK5)) != k4_waybel_1(sK5,X1) ),
% 0.86/1.03      inference(renaming,[status(thm)],[c_948]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_1072,plain,
% 0.86/1.03      ( ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
% 0.86/1.03      | r1_orders_2(sK5,X1,X2)
% 0.86/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X3,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 0.86/1.03      | X0 != X2
% 0.86/1.03      | k4_waybel_1(sK5,sK4(sK5)) != k4_waybel_1(sK5,X3)
% 0.86/1.03      | sK6 != X1
% 0.86/1.03      | sK5 != sK5 ),
% 0.86/1.03      inference(resolution_lifted,[status(thm)],[c_721,c_949]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_1073,plain,
% 0.86/1.03      ( ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
% 0.86/1.03      | r1_orders_2(sK5,sK6,X0)
% 0.86/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 0.86/1.03      | k4_waybel_1(sK5,sK4(sK5)) != k4_waybel_1(sK5,X1) ),
% 0.86/1.03      inference(unflattening,[status(thm)],[c_1072]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_1077,plain,
% 0.86/1.03      ( ~ m1_subset_1(X1,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 0.86/1.03      | r1_orders_2(sK5,sK6,X0)
% 0.86/1.03      | ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
% 0.86/1.03      | k4_waybel_1(sK5,sK4(sK5)) != k4_waybel_1(sK5,X1) ),
% 0.86/1.03      inference(global_propositional_subsumption,
% 0.86/1.03                [status(thm)],
% 0.86/1.03                [c_1073,c_33]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_1078,plain,
% 0.86/1.03      ( ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
% 0.86/1.03      | r1_orders_2(sK5,sK6,X0)
% 0.86/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 0.86/1.03      | k4_waybel_1(sK5,sK4(sK5)) != k4_waybel_1(sK5,X1) ),
% 0.86/1.03      inference(renaming,[status(thm)],[c_1077]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_3470,plain,
% 0.86/1.03      ( ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0_69)
% 0.86/1.03      | r1_orders_2(sK5,sK6,X0_69)
% 0.86/1.03      | ~ m1_subset_1(X1_69,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X0_69,u1_struct_0(sK5))
% 0.86/1.03      | k4_waybel_1(sK5,sK4(sK5)) != k4_waybel_1(sK5,X1_69) ),
% 0.86/1.03      inference(subtyping,[status(esa)],[c_1078]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_3483,plain,
% 0.86/1.03      ( sP1_iProver_split | sP0_iProver_split ),
% 0.86/1.03      inference(splitting,
% 0.86/1.03                [splitting(split),new_symbols(definition,[])],
% 0.86/1.03                [c_3470]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_3556,plain,
% 0.86/1.03      ( sP1_iProver_split = iProver_top
% 0.86/1.03      | sP0_iProver_split = iProver_top ),
% 0.86/1.03      inference(predicate_to_equality,[status(thm)],[c_3483]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_3482,plain,
% 0.86/1.03      ( ~ r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0_69)
% 0.86/1.03      | r1_orders_2(sK5,sK6,X0_69)
% 0.86/1.03      | ~ m1_subset_1(X0_69,u1_struct_0(sK5))
% 0.86/1.03      | ~ sP1_iProver_split ),
% 0.86/1.03      inference(splitting,
% 0.86/1.03                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 0.86/1.03                [c_3470]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_3557,plain,
% 0.86/1.03      ( r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0_69) != iProver_top
% 0.86/1.03      | r1_orders_2(sK5,sK6,X0_69) = iProver_top
% 0.86/1.03      | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top
% 0.86/1.03      | sP1_iProver_split != iProver_top ),
% 0.86/1.03      inference(predicate_to_equality,[status(thm)],[c_3482]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_3481,plain,
% 0.86/1.03      ( ~ m1_subset_1(X0_69,u1_struct_0(sK5))
% 0.86/1.03      | k4_waybel_1(sK5,sK4(sK5)) != k4_waybel_1(sK5,X0_69)
% 0.86/1.03      | ~ sP0_iProver_split ),
% 0.86/1.03      inference(splitting,
% 0.86/1.03                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 0.86/1.03                [c_3470]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_3974,plain,
% 0.86/1.03      ( k4_waybel_1(sK5,sK4(sK5)) != k4_waybel_1(sK5,X0_69)
% 0.86/1.03      | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top
% 0.86/1.03      | sP0_iProver_split != iProver_top ),
% 0.86/1.03      inference(predicate_to_equality,[status(thm)],[c_3481]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_4511,plain,
% 0.86/1.03      ( m1_subset_1(sK4(sK5),u1_struct_0(sK5)) != iProver_top
% 0.86/1.03      | sP0_iProver_split != iProver_top ),
% 0.86/1.03      inference(equality_resolution,[status(thm)],[c_3974]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_4559,plain,
% 0.86/1.03      ( m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top
% 0.86/1.03      | r1_orders_2(sK5,sK6,X0_69) = iProver_top
% 0.86/1.03      | r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0_69) != iProver_top ),
% 0.86/1.03      inference(global_propositional_subsumption,
% 0.86/1.03                [status(thm)],
% 0.86/1.03                [c_3971,c_3553,c_3556,c_3557,c_4511]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_4560,plain,
% 0.86/1.03      ( r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0_69) != iProver_top
% 0.86/1.03      | r1_orders_2(sK5,sK6,X0_69) = iProver_top
% 0.86/1.03      | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top ),
% 0.86/1.03      inference(renaming,[status(thm)],[c_4559]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_17,plain,
% 0.86/1.03      ( ~ l1_waybel_0(X0,X1)
% 0.86/1.03      | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 0.86/1.03      | ~ l1_struct_0(X1) ),
% 0.86/1.03      inference(cnf_transformation,[],[f81]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_2,plain,
% 0.86/1.03      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 0.86/1.03      inference(cnf_transformation,[],[f66]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_465,plain,
% 0.86/1.03      ( ~ l1_waybel_0(X0,X1)
% 0.86/1.03      | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 0.86/1.03      | ~ l1_orders_2(X2)
% 0.86/1.03      | X2 != X1 ),
% 0.86/1.03      inference(resolution_lifted,[status(thm)],[c_17,c_2]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_466,plain,
% 0.86/1.03      ( ~ l1_waybel_0(X0,X1)
% 0.86/1.03      | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 0.86/1.03      | ~ l1_orders_2(X1) ),
% 0.86/1.03      inference(unflattening,[status(thm)],[c_465]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_851,plain,
% 0.86/1.03      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
% 0.86/1.03      | ~ l1_orders_2(X0)
% 0.86/1.03      | sK7 != X1
% 0.86/1.03      | sK5 != X0 ),
% 0.86/1.03      inference(resolution_lifted,[status(thm)],[c_466,c_29]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_852,plain,
% 0.86/1.03      ( m1_subset_1(u1_waybel_0(sK5,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))
% 0.86/1.03      | ~ l1_orders_2(sK5) ),
% 0.86/1.03      inference(unflattening,[status(thm)],[c_851]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_854,plain,
% 0.86/1.03      ( m1_subset_1(u1_waybel_0(sK5,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) ),
% 0.86/1.03      inference(global_propositional_subsumption,
% 0.86/1.03                [status(thm)],
% 0.86/1.03                [c_852,c_34,c_75]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_3476,plain,
% 0.86/1.03      ( m1_subset_1(u1_waybel_0(sK5,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) ),
% 0.86/1.03      inference(subtyping,[status(esa)],[c_854]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_3967,plain,
% 0.86/1.03      ( m1_subset_1(u1_waybel_0(sK5,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) = iProver_top ),
% 0.86/1.03      inference(predicate_to_equality,[status(thm)],[c_3476]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_1,plain,
% 0.86/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.86/1.03      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 0.86/1.03      inference(cnf_transformation,[],[f65]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_3479,plain,
% 0.86/1.03      ( ~ m1_subset_1(X0_69,k1_zfmisc_1(k2_zfmisc_1(X0_72,X1_72)))
% 0.86/1.03      | k2_relset_1(X0_72,X1_72,X0_69) = k2_relat_1(X0_69) ),
% 0.86/1.03      inference(subtyping,[status(esa)],[c_1]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_3965,plain,
% 0.86/1.03      ( k2_relset_1(X0_72,X1_72,X0_69) = k2_relat_1(X0_69)
% 0.86/1.03      | m1_subset_1(X0_69,k1_zfmisc_1(k2_zfmisc_1(X0_72,X1_72))) != iProver_top ),
% 0.86/1.03      inference(predicate_to_equality,[status(thm)],[c_3479]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_4247,plain,
% 0.86/1.03      ( k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)) = k2_relat_1(u1_waybel_0(sK5,sK7)) ),
% 0.86/1.03      inference(superposition,[status(thm)],[c_3967,c_3965]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_4565,plain,
% 0.86/1.03      ( r2_lattice3(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69) != iProver_top
% 0.86/1.03      | r1_orders_2(sK5,sK6,X0_69) = iProver_top
% 0.86/1.03      | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top ),
% 0.86/1.03      inference(light_normalisation,[status(thm)],[c_4560,c_4247]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_4692,plain,
% 0.86/1.03      ( k1_yellow_0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7))) = X0_69
% 0.86/1.03      | r2_lattice3(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69) != iProver_top
% 0.86/1.03      | r1_orders_2(sK5,sK6,sK0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69)) = iProver_top
% 0.86/1.03      | r1_yellow_0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7))) != iProver_top
% 0.86/1.03      | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top
% 0.86/1.03      | m1_subset_1(sK0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69),u1_struct_0(sK5)) != iProver_top ),
% 0.86/1.03      inference(superposition,[status(thm)],[c_3984,c_4565]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_0,plain,
% 0.86/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.86/1.03      | v1_relat_1(X0) ),
% 0.86/1.03      inference(cnf_transformation,[],[f64]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_3480,plain,
% 0.86/1.03      ( ~ m1_subset_1(X0_69,k1_zfmisc_1(k2_zfmisc_1(X0_72,X1_72)))
% 0.86/1.03      | v1_relat_1(X0_69) ),
% 0.86/1.03      inference(subtyping,[status(esa)],[c_0]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_3964,plain,
% 0.86/1.03      ( m1_subset_1(X0_69,k1_zfmisc_1(k2_zfmisc_1(X0_72,X1_72))) != iProver_top
% 0.86/1.03      | v1_relat_1(X0_69) = iProver_top ),
% 0.86/1.03      inference(predicate_to_equality,[status(thm)],[c_3480]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_4242,plain,
% 0.86/1.03      ( v1_relat_1(u1_waybel_0(sK5,sK7)) = iProver_top ),
% 0.86/1.03      inference(superposition,[status(thm)],[c_3967,c_3964]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_19,plain,
% 0.86/1.03      ( v2_struct_0(X0)
% 0.86/1.03      | ~ l1_orders_2(X0)
% 0.86/1.03      | ~ v1_relat_1(X1)
% 0.86/1.03      | k1_yellow_0(X0,k2_relat_1(X1)) = k4_yellow_2(X0,X1) ),
% 0.86/1.03      inference(cnf_transformation,[],[f83]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_702,plain,
% 0.86/1.03      ( ~ v2_struct_0(X0) | ~ l1_orders_2(X0) | sK5 != X0 ),
% 0.86/1.03      inference(resolution_lifted,[status(thm)],[c_5,c_37]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_703,plain,
% 0.86/1.03      ( ~ v2_struct_0(sK5) | ~ l1_orders_2(sK5) ),
% 0.86/1.03      inference(unflattening,[status(thm)],[c_702]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_705,plain,
% 0.86/1.03      ( ~ v2_struct_0(sK5) ),
% 0.86/1.03      inference(global_propositional_subsumption,
% 0.86/1.03                [status(thm)],
% 0.86/1.03                [c_703,c_37,c_34,c_75,c_120]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_888,plain,
% 0.86/1.03      ( ~ l1_orders_2(X0)
% 0.86/1.03      | ~ v1_relat_1(X1)
% 0.86/1.03      | k1_yellow_0(X0,k2_relat_1(X1)) = k4_yellow_2(X0,X1)
% 0.86/1.03      | sK5 != X0 ),
% 0.86/1.03      inference(resolution_lifted,[status(thm)],[c_19,c_705]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_889,plain,
% 0.86/1.03      ( ~ l1_orders_2(sK5)
% 0.86/1.03      | ~ v1_relat_1(X0)
% 0.86/1.03      | k1_yellow_0(sK5,k2_relat_1(X0)) = k4_yellow_2(sK5,X0) ),
% 0.86/1.03      inference(unflattening,[status(thm)],[c_888]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_893,plain,
% 0.86/1.03      ( ~ v1_relat_1(X0)
% 0.86/1.03      | k1_yellow_0(sK5,k2_relat_1(X0)) = k4_yellow_2(sK5,X0) ),
% 0.86/1.03      inference(global_propositional_subsumption,
% 0.86/1.03                [status(thm)],
% 0.86/1.03                [c_889,c_34,c_75]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_3474,plain,
% 0.86/1.03      ( ~ v1_relat_1(X0_69)
% 0.86/1.03      | k1_yellow_0(sK5,k2_relat_1(X0_69)) = k4_yellow_2(sK5,X0_69) ),
% 0.86/1.03      inference(subtyping,[status(esa)],[c_893]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_3968,plain,
% 0.86/1.03      ( k1_yellow_0(sK5,k2_relat_1(X0_69)) = k4_yellow_2(sK5,X0_69)
% 0.86/1.03      | v1_relat_1(X0_69) != iProver_top ),
% 0.86/1.03      inference(predicate_to_equality,[status(thm)],[c_3474]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_4470,plain,
% 0.86/1.03      ( k1_yellow_0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7))) = k4_yellow_2(sK5,u1_waybel_0(sK5,sK7)) ),
% 0.86/1.03      inference(superposition,[status(thm)],[c_4242,c_3968]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_18,plain,
% 0.86/1.03      ( ~ l1_waybel_0(X0,X1)
% 0.86/1.03      | v2_struct_0(X1)
% 0.86/1.03      | ~ l1_orders_2(X1)
% 0.86/1.03      | k4_yellow_2(X1,u1_waybel_0(X1,X0)) = k1_waybel_2(X1,X0) ),
% 0.86/1.03      inference(cnf_transformation,[],[f82]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_862,plain,
% 0.86/1.03      ( v2_struct_0(X0)
% 0.86/1.03      | ~ l1_orders_2(X0)
% 0.86/1.03      | k4_yellow_2(X0,u1_waybel_0(X0,X1)) = k1_waybel_2(X0,X1)
% 0.86/1.03      | sK7 != X1
% 0.86/1.03      | sK5 != X0 ),
% 0.86/1.03      inference(resolution_lifted,[status(thm)],[c_18,c_29]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_863,plain,
% 0.86/1.03      ( v2_struct_0(sK5)
% 0.86/1.03      | ~ l1_orders_2(sK5)
% 0.86/1.03      | k4_yellow_2(sK5,u1_waybel_0(sK5,sK7)) = k1_waybel_2(sK5,sK7) ),
% 0.86/1.03      inference(unflattening,[status(thm)],[c_862]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_865,plain,
% 0.86/1.03      ( k4_yellow_2(sK5,u1_waybel_0(sK5,sK7)) = k1_waybel_2(sK5,sK7) ),
% 0.86/1.03      inference(global_propositional_subsumption,
% 0.86/1.03                [status(thm)],
% 0.86/1.03                [c_863,c_37,c_34,c_75,c_120]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_3475,plain,
% 0.86/1.03      ( k4_yellow_2(sK5,u1_waybel_0(sK5,sK7)) = k1_waybel_2(sK5,sK7) ),
% 0.86/1.03      inference(subtyping,[status(esa)],[c_865]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_4471,plain,
% 0.86/1.03      ( k1_yellow_0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7))) = k1_waybel_2(sK5,sK7) ),
% 0.86/1.03      inference(light_normalisation,[status(thm)],[c_4470,c_3475]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_4693,plain,
% 0.86/1.03      ( k1_waybel_2(sK5,sK7) = X0_69
% 0.86/1.03      | r2_lattice3(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69) != iProver_top
% 0.86/1.03      | r1_orders_2(sK5,sK6,sK0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69)) = iProver_top
% 0.86/1.03      | r1_yellow_0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7))) != iProver_top
% 0.86/1.03      | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top
% 0.86/1.03      | m1_subset_1(sK0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69),u1_struct_0(sK5)) != iProver_top ),
% 0.86/1.03      inference(demodulation,[status(thm)],[c_4692,c_4471]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_52,plain,
% 0.86/1.03      ( m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
% 0.86/1.03      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_21,plain,
% 0.86/1.03      ( ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
% 0.86/1.03      | ~ r3_waybel_9(X0,X1,X2)
% 0.86/1.03      | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
% 0.86/1.03      | ~ v10_waybel_0(X1,X0)
% 0.86/1.03      | ~ l1_waybel_0(X1,X0)
% 0.86/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.86/1.03      | ~ v2_pre_topc(X0)
% 0.86/1.03      | ~ v8_pre_topc(X0)
% 0.86/1.03      | ~ v2_lattice3(X0)
% 0.86/1.03      | ~ v1_compts_1(X0)
% 0.86/1.03      | ~ v4_orders_2(X1)
% 0.86/1.03      | ~ v4_orders_2(X0)
% 0.86/1.03      | ~ v7_waybel_0(X1)
% 0.86/1.03      | ~ l1_waybel_9(X0)
% 0.86/1.03      | ~ v5_orders_2(X0)
% 0.86/1.03      | ~ v1_lattice3(X0)
% 0.86/1.03      | v2_struct_0(X1)
% 0.86/1.03      | ~ v3_orders_2(X0) ),
% 0.86/1.03      inference(cnf_transformation,[],[f109]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_27,negated_conjecture,
% 0.86/1.03      ( v10_waybel_0(sK7,sK5) ),
% 0.86/1.03      inference(cnf_transformation,[],[f104]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_530,plain,
% 0.86/1.03      ( ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
% 0.86/1.03      | ~ r3_waybel_9(X0,X1,X2)
% 0.86/1.03      | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
% 0.86/1.03      | ~ l1_waybel_0(X1,X0)
% 0.86/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.86/1.03      | ~ v2_pre_topc(X0)
% 0.86/1.03      | ~ v8_pre_topc(X0)
% 0.86/1.03      | ~ v2_lattice3(X0)
% 0.86/1.03      | ~ v1_compts_1(X0)
% 0.86/1.03      | ~ v4_orders_2(X1)
% 0.86/1.03      | ~ v4_orders_2(X0)
% 0.86/1.03      | ~ v7_waybel_0(X1)
% 0.86/1.03      | ~ l1_waybel_9(X0)
% 0.86/1.03      | ~ v5_orders_2(X0)
% 0.86/1.03      | ~ v1_lattice3(X0)
% 0.86/1.03      | v2_struct_0(X1)
% 0.86/1.03      | ~ v3_orders_2(X0)
% 0.86/1.03      | sK7 != X1
% 0.86/1.03      | sK5 != X0 ),
% 0.86/1.03      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_531,plain,
% 0.86/1.03      ( ~ v5_pre_topc(k4_waybel_1(sK5,sK3(sK5)),sK5,sK5)
% 0.86/1.03      | ~ r3_waybel_9(sK5,sK7,X0)
% 0.86/1.03      | r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
% 0.86/1.03      | ~ l1_waybel_0(sK7,sK5)
% 0.86/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 0.86/1.03      | ~ v2_pre_topc(sK5)
% 0.86/1.03      | ~ v8_pre_topc(sK5)
% 0.86/1.03      | ~ v2_lattice3(sK5)
% 0.86/1.03      | ~ v1_compts_1(sK5)
% 0.86/1.03      | ~ v4_orders_2(sK7)
% 0.86/1.03      | ~ v4_orders_2(sK5)
% 0.86/1.03      | ~ v7_waybel_0(sK7)
% 0.86/1.03      | ~ l1_waybel_9(sK5)
% 0.86/1.03      | ~ v5_orders_2(sK5)
% 0.86/1.03      | ~ v1_lattice3(sK5)
% 0.86/1.03      | v2_struct_0(sK7)
% 0.86/1.03      | ~ v3_orders_2(sK5) ),
% 0.86/1.03      inference(unflattening,[status(thm)],[c_530]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_535,plain,
% 0.86/1.03      ( r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
% 0.86/1.03      | ~ r3_waybel_9(sK5,sK7,X0)
% 0.86/1.03      | ~ v5_pre_topc(k4_waybel_1(sK5,sK3(sK5)),sK5,sK5)
% 0.86/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 0.86/1.03      inference(global_propositional_subsumption,
% 0.86/1.03                [status(thm)],
% 0.86/1.03                [c_531,c_42,c_41,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_32,
% 0.86/1.03                 c_31,c_30,c_29]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_536,plain,
% 0.86/1.03      ( ~ v5_pre_topc(k4_waybel_1(sK5,sK3(sK5)),sK5,sK5)
% 0.86/1.03      | ~ r3_waybel_9(sK5,sK7,X0)
% 0.86/1.03      | r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
% 0.86/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 0.86/1.03      inference(renaming,[status(thm)],[c_535]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_609,plain,
% 0.86/1.03      ( ~ r3_waybel_9(sK5,sK7,X0)
% 0.86/1.03      | r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
% 0.86/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 0.86/1.03      | k4_waybel_1(sK5,sK3(sK5)) != k4_waybel_1(sK5,X1)
% 0.86/1.03      | sK5 != sK5 ),
% 0.86/1.03      inference(resolution_lifted,[status(thm)],[c_28,c_536]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_994,plain,
% 0.86/1.03      ( r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
% 0.86/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 0.86/1.03      | k4_waybel_1(sK5,sK3(sK5)) != k4_waybel_1(sK5,X1)
% 0.86/1.03      | sK6 != X0
% 0.86/1.03      | sK7 != sK7
% 0.86/1.03      | sK5 != sK5 ),
% 0.86/1.03      inference(resolution_lifted,[status(thm)],[c_26,c_609]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_995,plain,
% 0.86/1.03      ( r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),sK6)
% 0.86/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 0.86/1.03      | k4_waybel_1(sK5,sK3(sK5)) != k4_waybel_1(sK5,X0) ),
% 0.86/1.03      inference(unflattening,[status(thm)],[c_994]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_999,plain,
% 0.86/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 0.86/1.03      | r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),sK6)
% 0.86/1.03      | k4_waybel_1(sK5,sK3(sK5)) != k4_waybel_1(sK5,X0) ),
% 0.86/1.03      inference(global_propositional_subsumption,
% 0.86/1.03                [status(thm)],
% 0.86/1.03                [c_995,c_33]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_1000,plain,
% 0.86/1.03      ( r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),sK6)
% 0.86/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 0.86/1.03      | k4_waybel_1(sK5,sK3(sK5)) != k4_waybel_1(sK5,X0) ),
% 0.86/1.03      inference(renaming,[status(thm)],[c_999]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_3473,plain,
% 0.86/1.03      ( r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),sK6)
% 0.86/1.03      | ~ m1_subset_1(X0_69,u1_struct_0(sK5))
% 0.86/1.03      | k4_waybel_1(sK5,sK3(sK5)) != k4_waybel_1(sK5,X0_69) ),
% 0.86/1.03      inference(subtyping,[status(esa)],[c_1000]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_3969,plain,
% 0.86/1.03      ( k4_waybel_1(sK5,sK3(sK5)) != k4_waybel_1(sK5,X0_69)
% 0.86/1.03      | r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),sK6) = iProver_top
% 0.86/1.03      | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top ),
% 0.86/1.03      inference(predicate_to_equality,[status(thm)],[c_3473]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_22,plain,
% 0.86/1.03      ( ~ r3_waybel_9(X0,X1,X2)
% 0.86/1.03      | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
% 0.86/1.03      | ~ v10_waybel_0(X1,X0)
% 0.86/1.03      | ~ l1_waybel_0(X1,X0)
% 0.86/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.86/1.03      | m1_subset_1(sK3(X0),u1_struct_0(X0))
% 0.86/1.03      | ~ v2_pre_topc(X0)
% 0.86/1.03      | ~ v8_pre_topc(X0)
% 0.86/1.03      | ~ v2_lattice3(X0)
% 0.86/1.03      | ~ v1_compts_1(X0)
% 0.86/1.03      | ~ v4_orders_2(X1)
% 0.86/1.03      | ~ v4_orders_2(X0)
% 0.86/1.03      | ~ v7_waybel_0(X1)
% 0.86/1.03      | ~ l1_waybel_9(X0)
% 0.86/1.03      | ~ v5_orders_2(X0)
% 0.86/1.03      | ~ v1_lattice3(X0)
% 0.86/1.03      | v2_struct_0(X1)
% 0.86/1.03      | ~ v3_orders_2(X0) ),
% 0.86/1.03      inference(cnf_transformation,[],[f110]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_506,plain,
% 0.86/1.03      ( ~ r3_waybel_9(X0,X1,X2)
% 0.86/1.03      | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
% 0.86/1.03      | ~ l1_waybel_0(X1,X0)
% 0.86/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.86/1.03      | m1_subset_1(sK3(X0),u1_struct_0(X0))
% 0.86/1.03      | ~ v2_pre_topc(X0)
% 0.86/1.03      | ~ v8_pre_topc(X0)
% 0.86/1.03      | ~ v2_lattice3(X0)
% 0.86/1.03      | ~ v1_compts_1(X0)
% 0.86/1.03      | ~ v4_orders_2(X1)
% 0.86/1.03      | ~ v4_orders_2(X0)
% 0.86/1.03      | ~ v7_waybel_0(X1)
% 0.86/1.03      | ~ l1_waybel_9(X0)
% 0.86/1.03      | ~ v5_orders_2(X0)
% 0.86/1.03      | ~ v1_lattice3(X0)
% 0.86/1.03      | v2_struct_0(X1)
% 0.86/1.03      | ~ v3_orders_2(X0)
% 0.86/1.03      | sK7 != X1
% 0.86/1.03      | sK5 != X0 ),
% 0.86/1.03      inference(resolution_lifted,[status(thm)],[c_22,c_27]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_507,plain,
% 0.86/1.03      ( ~ r3_waybel_9(sK5,sK7,X0)
% 0.86/1.03      | r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
% 0.86/1.03      | ~ l1_waybel_0(sK7,sK5)
% 0.86/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 0.86/1.03      | m1_subset_1(sK3(sK5),u1_struct_0(sK5))
% 0.86/1.03      | ~ v2_pre_topc(sK5)
% 0.86/1.03      | ~ v8_pre_topc(sK5)
% 0.86/1.03      | ~ v2_lattice3(sK5)
% 0.86/1.03      | ~ v1_compts_1(sK5)
% 0.86/1.03      | ~ v4_orders_2(sK7)
% 0.86/1.03      | ~ v4_orders_2(sK5)
% 0.86/1.03      | ~ v7_waybel_0(sK7)
% 0.86/1.03      | ~ l1_waybel_9(sK5)
% 0.86/1.03      | ~ v5_orders_2(sK5)
% 0.86/1.03      | ~ v1_lattice3(sK5)
% 0.86/1.03      | v2_struct_0(sK7)
% 0.86/1.03      | ~ v3_orders_2(sK5) ),
% 0.86/1.03      inference(unflattening,[status(thm)],[c_506]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_511,plain,
% 0.86/1.03      ( r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
% 0.86/1.03      | ~ r3_waybel_9(sK5,sK7,X0)
% 0.86/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 0.86/1.03      | m1_subset_1(sK3(sK5),u1_struct_0(sK5)) ),
% 0.86/1.03      inference(global_propositional_subsumption,
% 0.86/1.03                [status(thm)],
% 0.86/1.03                [c_507,c_42,c_41,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_32,
% 0.86/1.03                 c_31,c_30,c_29]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_512,plain,
% 0.86/1.03      ( ~ r3_waybel_9(sK5,sK7,X0)
% 0.86/1.03      | r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
% 0.86/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 0.86/1.03      | m1_subset_1(sK3(sK5),u1_struct_0(sK5)) ),
% 0.86/1.03      inference(renaming,[status(thm)],[c_511]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_1015,plain,
% 0.86/1.03      ( r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),X0)
% 0.86/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 0.86/1.03      | m1_subset_1(sK3(sK5),u1_struct_0(sK5))
% 0.86/1.03      | sK6 != X0
% 0.86/1.03      | sK7 != sK7
% 0.86/1.03      | sK5 != sK5 ),
% 0.86/1.03      inference(resolution_lifted,[status(thm)],[c_26,c_512]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_1016,plain,
% 0.86/1.03      ( r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),sK6)
% 0.86/1.03      | m1_subset_1(sK3(sK5),u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 0.86/1.03      inference(unflattening,[status(thm)],[c_1015]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_1018,plain,
% 0.86/1.03      ( m1_subset_1(sK3(sK5),u1_struct_0(sK5))
% 0.86/1.03      | r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),sK6) ),
% 0.86/1.03      inference(global_propositional_subsumption,
% 0.86/1.03                [status(thm)],
% 0.86/1.03                [c_1016,c_33]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_1019,plain,
% 0.86/1.03      ( r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),sK6)
% 0.86/1.03      | m1_subset_1(sK3(sK5),u1_struct_0(sK5)) ),
% 0.86/1.03      inference(renaming,[status(thm)],[c_1018]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_1020,plain,
% 0.86/1.03      ( r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),sK6) = iProver_top
% 0.86/1.03      | m1_subset_1(sK3(sK5),u1_struct_0(sK5)) = iProver_top ),
% 0.86/1.03      inference(predicate_to_equality,[status(thm)],[c_1019]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_3489,plain,( X0_73 = X0_73 ),theory(equality) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_4191,plain,
% 0.86/1.03      ( k4_waybel_1(sK5,sK3(sK5)) = k4_waybel_1(sK5,sK3(sK5)) ),
% 0.86/1.03      inference(instantiation,[status(thm)],[c_3489]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_4192,plain,
% 0.86/1.03      ( r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),sK6)
% 0.86/1.03      | ~ m1_subset_1(sK3(sK5),u1_struct_0(sK5))
% 0.86/1.03      | k4_waybel_1(sK5,sK3(sK5)) != k4_waybel_1(sK5,sK3(sK5)) ),
% 0.86/1.03      inference(instantiation,[status(thm)],[c_3473]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_4193,plain,
% 0.86/1.03      ( k4_waybel_1(sK5,sK3(sK5)) != k4_waybel_1(sK5,sK3(sK5))
% 0.86/1.03      | r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),sK6) = iProver_top
% 0.86/1.03      | m1_subset_1(sK3(sK5),u1_struct_0(sK5)) != iProver_top ),
% 0.86/1.03      inference(predicate_to_equality,[status(thm)],[c_4192]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_4209,plain,
% 0.86/1.03      ( r2_lattice3(sK5,k2_relset_1(u1_struct_0(sK7),u1_struct_0(sK5),u1_waybel_0(sK5,sK7)),sK6) = iProver_top ),
% 0.86/1.03      inference(global_propositional_subsumption,
% 0.86/1.03                [status(thm)],
% 0.86/1.03                [c_3969,c_1020,c_4191,c_4193]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_4284,plain,
% 0.86/1.03      ( r2_lattice3(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),sK6) = iProver_top ),
% 0.86/1.03      inference(demodulation,[status(thm)],[c_4247,c_4209]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_12,plain,
% 0.86/1.03      ( ~ r2_lattice3(X0,X1,X2)
% 0.86/1.03      | r2_lattice3(X0,X1,sK1(X0,X1,X2))
% 0.86/1.03      | r1_yellow_0(X0,X1)
% 0.86/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.86/1.03      | ~ v5_orders_2(X0)
% 0.86/1.03      | ~ l1_orders_2(X0) ),
% 0.86/1.03      inference(cnf_transformation,[],[f79]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_1194,plain,
% 0.86/1.03      ( ~ r2_lattice3(X0,X1,X2)
% 0.86/1.03      | r2_lattice3(X0,X1,sK1(X0,X1,X2))
% 0.86/1.03      | r1_yellow_0(X0,X1)
% 0.86/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.86/1.03      | ~ l1_orders_2(X0)
% 0.86/1.03      | sK5 != X0 ),
% 0.86/1.03      inference(resolution_lifted,[status(thm)],[c_12,c_38]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_1195,plain,
% 0.86/1.03      ( ~ r2_lattice3(sK5,X0,X1)
% 0.86/1.03      | r2_lattice3(sK5,X0,sK1(sK5,X0,X1))
% 0.86/1.03      | r1_yellow_0(sK5,X0)
% 0.86/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 0.86/1.03      | ~ l1_orders_2(sK5) ),
% 0.86/1.03      inference(unflattening,[status(thm)],[c_1194]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_1199,plain,
% 0.86/1.03      ( ~ m1_subset_1(X1,u1_struct_0(sK5))
% 0.86/1.03      | r1_yellow_0(sK5,X0)
% 0.86/1.03      | r2_lattice3(sK5,X0,sK1(sK5,X0,X1))
% 0.86/1.03      | ~ r2_lattice3(sK5,X0,X1) ),
% 0.86/1.03      inference(global_propositional_subsumption,
% 0.86/1.03                [status(thm)],
% 0.86/1.03                [c_1195,c_34,c_75]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_1200,plain,
% 0.86/1.03      ( ~ r2_lattice3(sK5,X0,X1)
% 0.86/1.03      | r2_lattice3(sK5,X0,sK1(sK5,X0,X1))
% 0.86/1.03      | r1_yellow_0(sK5,X0)
% 0.86/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
% 0.86/1.03      inference(renaming,[status(thm)],[c_1199]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_3465,plain,
% 0.86/1.03      ( ~ r2_lattice3(sK5,X0_71,X0_69)
% 0.86/1.03      | r2_lattice3(sK5,X0_71,sK1(sK5,X0_71,X0_69))
% 0.86/1.03      | r1_yellow_0(sK5,X0_71)
% 0.86/1.03      | ~ m1_subset_1(X0_69,u1_struct_0(sK5)) ),
% 0.86/1.03      inference(subtyping,[status(esa)],[c_1200]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_3979,plain,
% 0.86/1.03      ( r2_lattice3(sK5,X0_71,X0_69) != iProver_top
% 0.86/1.03      | r2_lattice3(sK5,X0_71,sK1(sK5,X0_71,X0_69)) = iProver_top
% 0.86/1.03      | r1_yellow_0(sK5,X0_71) = iProver_top
% 0.86/1.03      | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top ),
% 0.86/1.03      inference(predicate_to_equality,[status(thm)],[c_3465]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_4572,plain,
% 0.86/1.03      ( r2_lattice3(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69) != iProver_top
% 0.86/1.03      | r1_orders_2(sK5,sK6,sK1(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69)) = iProver_top
% 0.86/1.03      | r1_yellow_0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7))) = iProver_top
% 0.86/1.03      | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top
% 0.86/1.03      | m1_subset_1(sK1(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69),u1_struct_0(sK5)) != iProver_top ),
% 0.86/1.03      inference(superposition,[status(thm)],[c_3979,c_4565]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_13,plain,
% 0.86/1.03      ( ~ r2_lattice3(X0,X1,X2)
% 0.86/1.03      | r1_yellow_0(X0,X1)
% 0.86/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.86/1.03      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 0.86/1.03      | ~ v5_orders_2(X0)
% 0.86/1.03      | ~ l1_orders_2(X0) ),
% 0.86/1.03      inference(cnf_transformation,[],[f78]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_1170,plain,
% 0.86/1.03      ( ~ r2_lattice3(X0,X1,X2)
% 0.86/1.03      | r1_yellow_0(X0,X1)
% 0.86/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.86/1.03      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 0.86/1.03      | ~ l1_orders_2(X0)
% 0.86/1.03      | sK5 != X0 ),
% 0.86/1.03      inference(resolution_lifted,[status(thm)],[c_13,c_38]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_1171,plain,
% 0.86/1.03      ( ~ r2_lattice3(sK5,X0,X1)
% 0.86/1.03      | r1_yellow_0(sK5,X0)
% 0.86/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 0.86/1.03      | m1_subset_1(sK1(sK5,X0,X1),u1_struct_0(sK5))
% 0.86/1.03      | ~ l1_orders_2(sK5) ),
% 0.86/1.03      inference(unflattening,[status(thm)],[c_1170]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_1175,plain,
% 0.86/1.03      ( m1_subset_1(sK1(sK5,X0,X1),u1_struct_0(sK5))
% 0.86/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 0.86/1.03      | r1_yellow_0(sK5,X0)
% 0.86/1.03      | ~ r2_lattice3(sK5,X0,X1) ),
% 0.86/1.03      inference(global_propositional_subsumption,
% 0.86/1.03                [status(thm)],
% 0.86/1.03                [c_1171,c_34,c_75]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_1176,plain,
% 0.86/1.03      ( ~ r2_lattice3(sK5,X0,X1)
% 0.86/1.03      | r1_yellow_0(sK5,X0)
% 0.86/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 0.86/1.03      | m1_subset_1(sK1(sK5,X0,X1),u1_struct_0(sK5)) ),
% 0.86/1.03      inference(renaming,[status(thm)],[c_1175]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_3466,plain,
% 0.86/1.03      ( ~ r2_lattice3(sK5,X0_71,X0_69)
% 0.86/1.03      | r1_yellow_0(sK5,X0_71)
% 0.86/1.03      | ~ m1_subset_1(X0_69,u1_struct_0(sK5))
% 0.86/1.03      | m1_subset_1(sK1(sK5,X0_71,X0_69),u1_struct_0(sK5)) ),
% 0.86/1.03      inference(subtyping,[status(esa)],[c_1176]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_3978,plain,
% 0.86/1.03      ( r2_lattice3(sK5,X0_71,X0_69) != iProver_top
% 0.86/1.03      | r1_yellow_0(sK5,X0_71) = iProver_top
% 0.86/1.03      | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top
% 0.86/1.03      | m1_subset_1(sK1(sK5,X0_71,X0_69),u1_struct_0(sK5)) = iProver_top ),
% 0.86/1.03      inference(predicate_to_equality,[status(thm)],[c_3466]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_5165,plain,
% 0.86/1.03      ( r2_lattice3(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69) != iProver_top
% 0.86/1.03      | r1_orders_2(sK5,sK6,sK1(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69)) = iProver_top
% 0.86/1.03      | r1_yellow_0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7))) = iProver_top
% 0.86/1.03      | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top ),
% 0.86/1.03      inference(forward_subsumption_resolution,
% 0.86/1.03                [status(thm)],
% 0.86/1.03                [c_4572,c_3978]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_11,plain,
% 0.86/1.03      ( ~ r2_lattice3(X0,X1,X2)
% 0.86/1.03      | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
% 0.86/1.03      | r1_yellow_0(X0,X1)
% 0.86/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.86/1.03      | ~ v5_orders_2(X0)
% 0.86/1.03      | ~ l1_orders_2(X0) ),
% 0.86/1.03      inference(cnf_transformation,[],[f80]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_1218,plain,
% 0.86/1.03      ( ~ r2_lattice3(X0,X1,X2)
% 0.86/1.03      | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
% 0.86/1.03      | r1_yellow_0(X0,X1)
% 0.86/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.86/1.03      | ~ l1_orders_2(X0)
% 0.86/1.03      | sK5 != X0 ),
% 0.86/1.03      inference(resolution_lifted,[status(thm)],[c_11,c_38]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_1219,plain,
% 0.86/1.03      ( ~ r2_lattice3(sK5,X0,X1)
% 0.86/1.03      | ~ r1_orders_2(sK5,X1,sK1(sK5,X0,X1))
% 0.86/1.03      | r1_yellow_0(sK5,X0)
% 0.86/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 0.86/1.03      | ~ l1_orders_2(sK5) ),
% 0.86/1.03      inference(unflattening,[status(thm)],[c_1218]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_1223,plain,
% 0.86/1.03      ( ~ m1_subset_1(X1,u1_struct_0(sK5))
% 0.86/1.03      | r1_yellow_0(sK5,X0)
% 0.86/1.03      | ~ r1_orders_2(sK5,X1,sK1(sK5,X0,X1))
% 0.86/1.03      | ~ r2_lattice3(sK5,X0,X1) ),
% 0.86/1.03      inference(global_propositional_subsumption,
% 0.86/1.03                [status(thm)],
% 0.86/1.03                [c_1219,c_34,c_75]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_1224,plain,
% 0.86/1.03      ( ~ r2_lattice3(sK5,X0,X1)
% 0.86/1.03      | ~ r1_orders_2(sK5,X1,sK1(sK5,X0,X1))
% 0.86/1.03      | r1_yellow_0(sK5,X0)
% 0.86/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
% 0.86/1.03      inference(renaming,[status(thm)],[c_1223]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_3464,plain,
% 0.86/1.03      ( ~ r2_lattice3(sK5,X0_71,X0_69)
% 0.86/1.03      | ~ r1_orders_2(sK5,X0_69,sK1(sK5,X0_71,X0_69))
% 0.86/1.03      | r1_yellow_0(sK5,X0_71)
% 0.86/1.03      | ~ m1_subset_1(X0_69,u1_struct_0(sK5)) ),
% 0.86/1.03      inference(subtyping,[status(esa)],[c_1224]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_3980,plain,
% 0.86/1.03      ( r2_lattice3(sK5,X0_71,X0_69) != iProver_top
% 0.86/1.03      | r1_orders_2(sK5,X0_69,sK1(sK5,X0_71,X0_69)) != iProver_top
% 0.86/1.03      | r1_yellow_0(sK5,X0_71) = iProver_top
% 0.86/1.03      | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top ),
% 0.86/1.03      inference(predicate_to_equality,[status(thm)],[c_3464]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_5169,plain,
% 0.86/1.03      ( r2_lattice3(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),sK6) != iProver_top
% 0.86/1.03      | r1_yellow_0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7))) = iProver_top
% 0.86/1.03      | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
% 0.86/1.03      inference(superposition,[status(thm)],[c_5165,c_3980]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_5378,plain,
% 0.86/1.03      ( r1_orders_2(sK5,sK6,sK0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69)) = iProver_top
% 0.86/1.03      | r2_lattice3(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69) != iProver_top
% 0.86/1.03      | k1_waybel_2(sK5,sK7) = X0_69
% 0.86/1.03      | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top
% 0.86/1.03      | m1_subset_1(sK0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69),u1_struct_0(sK5)) != iProver_top ),
% 0.86/1.03      inference(global_propositional_subsumption,
% 0.86/1.03                [status(thm)],
% 0.86/1.03                [c_4693,c_52,c_4284,c_5169]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_5379,plain,
% 0.86/1.03      ( k1_waybel_2(sK5,sK7) = X0_69
% 0.86/1.03      | r2_lattice3(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69) != iProver_top
% 0.86/1.03      | r1_orders_2(sK5,sK6,sK0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69)) = iProver_top
% 0.86/1.03      | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top
% 0.86/1.03      | m1_subset_1(sK0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69),u1_struct_0(sK5)) != iProver_top ),
% 0.86/1.03      inference(renaming,[status(thm)],[c_5378]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_5389,plain,
% 0.86/1.03      ( k1_waybel_2(sK5,sK7) = X0_69
% 0.86/1.03      | k1_yellow_0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7))) = X0_69
% 0.86/1.03      | r2_lattice3(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69) != iProver_top
% 0.86/1.03      | r1_orders_2(sK5,sK6,sK0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69)) = iProver_top
% 0.86/1.03      | r1_yellow_0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7))) != iProver_top
% 0.86/1.03      | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top ),
% 0.86/1.03      inference(superposition,[status(thm)],[c_3983,c_5379]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_5390,plain,
% 0.86/1.03      ( k1_waybel_2(sK5,sK7) = X0_69
% 0.86/1.03      | r2_lattice3(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69) != iProver_top
% 0.86/1.03      | r1_orders_2(sK5,sK6,sK0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69)) = iProver_top
% 0.86/1.03      | r1_yellow_0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7))) != iProver_top
% 0.86/1.03      | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top ),
% 0.86/1.03      inference(demodulation,[status(thm)],[c_5389,c_4471]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_5437,plain,
% 0.86/1.03      ( r1_orders_2(sK5,sK6,sK0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69)) = iProver_top
% 0.86/1.03      | r2_lattice3(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69) != iProver_top
% 0.86/1.03      | k1_waybel_2(sK5,sK7) = X0_69
% 0.86/1.03      | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top ),
% 0.86/1.03      inference(global_propositional_subsumption,
% 0.86/1.03                [status(thm)],
% 0.86/1.03                [c_5390,c_52,c_4284,c_5169]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_5438,plain,
% 0.86/1.03      ( k1_waybel_2(sK5,sK7) = X0_69
% 0.86/1.03      | r2_lattice3(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69) != iProver_top
% 0.86/1.03      | r1_orders_2(sK5,sK6,sK0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),X0_69)) = iProver_top
% 0.86/1.03      | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top ),
% 0.86/1.03      inference(renaming,[status(thm)],[c_5437]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_6,plain,
% 0.86/1.03      ( ~ r2_lattice3(X0,X1,X2)
% 0.86/1.03      | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
% 0.86/1.03      | ~ r1_yellow_0(X0,X1)
% 0.86/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.86/1.03      | ~ l1_orders_2(X0)
% 0.86/1.03      | k1_yellow_0(X0,X1) = X2 ),
% 0.86/1.03      inference(cnf_transformation,[],[f74]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_1346,plain,
% 0.86/1.03      ( ~ r2_lattice3(X0,X1,X2)
% 0.86/1.03      | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
% 0.86/1.03      | ~ r1_yellow_0(X0,X1)
% 0.86/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.86/1.03      | k1_yellow_0(X0,X1) = X2
% 0.86/1.03      | sK5 != X0 ),
% 0.86/1.03      inference(resolution_lifted,[status(thm)],[c_6,c_694]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_1347,plain,
% 0.86/1.03      ( ~ r2_lattice3(sK5,X0,X1)
% 0.86/1.03      | ~ r1_orders_2(sK5,X1,sK0(sK5,X0,X1))
% 0.86/1.03      | ~ r1_yellow_0(sK5,X0)
% 0.86/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 0.86/1.03      | k1_yellow_0(sK5,X0) = X1 ),
% 0.86/1.03      inference(unflattening,[status(thm)],[c_1346]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_3459,plain,
% 0.86/1.03      ( ~ r2_lattice3(sK5,X0_71,X0_69)
% 0.86/1.03      | ~ r1_orders_2(sK5,X0_69,sK0(sK5,X0_71,X0_69))
% 0.86/1.03      | ~ r1_yellow_0(sK5,X0_71)
% 0.86/1.03      | ~ m1_subset_1(X0_69,u1_struct_0(sK5))
% 0.86/1.03      | k1_yellow_0(sK5,X0_71) = X0_69 ),
% 0.86/1.03      inference(subtyping,[status(esa)],[c_1347]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_3985,plain,
% 0.86/1.03      ( k1_yellow_0(sK5,X0_71) = X0_69
% 0.86/1.03      | r2_lattice3(sK5,X0_71,X0_69) != iProver_top
% 0.86/1.03      | r1_orders_2(sK5,X0_69,sK0(sK5,X0_71,X0_69)) != iProver_top
% 0.86/1.03      | r1_yellow_0(sK5,X0_71) != iProver_top
% 0.86/1.03      | m1_subset_1(X0_69,u1_struct_0(sK5)) != iProver_top ),
% 0.86/1.03      inference(predicate_to_equality,[status(thm)],[c_3459]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_5447,plain,
% 0.86/1.03      ( k1_waybel_2(sK5,sK7) = sK6
% 0.86/1.03      | k1_yellow_0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7))) = sK6
% 0.86/1.03      | r2_lattice3(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),sK6) != iProver_top
% 0.86/1.03      | r1_yellow_0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7))) != iProver_top
% 0.86/1.03      | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
% 0.86/1.03      inference(superposition,[status(thm)],[c_5438,c_3985]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_5448,plain,
% 0.86/1.03      ( k1_waybel_2(sK5,sK7) = sK6
% 0.86/1.03      | r2_lattice3(sK5,k2_relat_1(u1_waybel_0(sK5,sK7)),sK6) != iProver_top
% 0.86/1.03      | r1_yellow_0(sK5,k2_relat_1(u1_waybel_0(sK5,sK7))) != iProver_top
% 0.86/1.03      | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
% 0.86/1.03      inference(demodulation,[status(thm)],[c_5447,c_4471]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_25,negated_conjecture,
% 0.86/1.03      ( k1_waybel_2(sK5,sK7) != sK6 ),
% 0.86/1.03      inference(cnf_transformation,[],[f106]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(c_3478,negated_conjecture,
% 0.86/1.03      ( k1_waybel_2(sK5,sK7) != sK6 ),
% 0.86/1.03      inference(subtyping,[status(esa)],[c_25]) ).
% 0.86/1.03  
% 0.86/1.03  cnf(contradiction,plain,
% 0.86/1.03      ( $false ),
% 0.86/1.03      inference(minisat,[status(thm)],[c_5448,c_5169,c_4284,c_3478,c_52]) ).
% 0.86/1.03  
% 0.86/1.03  
% 0.86/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 0.86/1.03  
% 0.86/1.03  ------                               Statistics
% 0.86/1.03  
% 0.86/1.03  ------ General
% 0.86/1.03  
% 0.86/1.03  abstr_ref_over_cycles:                  0
% 0.86/1.03  abstr_ref_under_cycles:                 0
% 0.86/1.03  gc_basic_clause_elim:                   0
% 0.86/1.03  forced_gc_time:                         0
% 0.86/1.03  parsing_time:                           0.008
% 0.86/1.03  unif_index_cands_time:                  0.
% 0.86/1.03  unif_index_add_time:                    0.
% 0.86/1.03  orderings_time:                         0.
% 0.86/1.03  out_proof_time:                         0.021
% 0.86/1.03  total_time:                             0.156
% 0.86/1.03  num_of_symbols:                         77
% 0.86/1.03  num_of_terms:                           3246
% 0.86/1.03  
% 0.86/1.03  ------ Preprocessing
% 0.86/1.03  
% 0.86/1.03  num_of_splits:                          2
% 0.86/1.03  num_of_split_atoms:                     2
% 0.86/1.03  num_of_reused_defs:                     0
% 0.86/1.03  num_eq_ax_congr_red:                    41
% 0.86/1.03  num_of_sem_filtered_clauses:            1
% 0.86/1.03  num_of_subtypes:                        6
% 0.86/1.03  monotx_restored_types:                  0
% 0.86/1.03  sat_num_of_epr_types:                   0
% 0.86/1.03  sat_num_of_non_cyclic_types:            0
% 0.86/1.03  sat_guarded_non_collapsed_types:        1
% 0.86/1.03  num_pure_diseq_elim:                    0
% 0.86/1.03  simp_replaced_by:                       0
% 0.86/1.03  res_preprocessed:                       173
% 0.86/1.03  prep_upred:                             0
% 0.86/1.03  prep_unflattend:                        71
% 0.86/1.03  smt_new_axioms:                         0
% 0.86/1.03  pred_elim_cands:                        5
% 0.86/1.03  pred_elim:                              18
% 0.86/1.03  pred_elim_cl:                           20
% 0.86/1.03  pred_elim_cycles:                       26
% 0.86/1.03  merged_defs:                            0
% 0.86/1.03  merged_defs_ncl:                        0
% 0.86/1.03  bin_hyper_res:                          0
% 0.86/1.03  prep_cycles:                            4
% 0.86/1.03  pred_elim_time:                         0.035
% 0.86/1.03  splitting_time:                         0.
% 0.86/1.03  sem_filter_time:                        0.
% 0.86/1.03  monotx_time:                            0.
% 0.86/1.03  subtype_inf_time:                       0.
% 0.86/1.03  
% 0.86/1.03  ------ Problem properties
% 0.86/1.03  
% 0.86/1.03  clauses:                                25
% 0.86/1.03  conjectures:                            2
% 0.86/1.03  epr:                                    1
% 0.86/1.03  horn:                                   18
% 0.86/1.03  ground:                                 6
% 0.86/1.03  unary:                                  4
% 0.86/1.03  binary:                                 7
% 0.86/1.03  lits:                                   74
% 0.86/1.03  lits_eq:                                11
% 0.86/1.03  fd_pure:                                0
% 0.86/1.03  fd_pseudo:                              0
% 0.86/1.03  fd_cond:                                0
% 0.86/1.03  fd_pseudo_cond:                         3
% 0.86/1.03  ac_symbols:                             0
% 0.86/1.03  
% 0.86/1.03  ------ Propositional Solver
% 0.86/1.03  
% 0.86/1.03  prop_solver_calls:                      27
% 0.86/1.03  prop_fast_solver_calls:                 2073
% 0.86/1.03  smt_solver_calls:                       0
% 0.86/1.03  smt_fast_solver_calls:                  0
% 0.86/1.03  prop_num_of_clauses:                    1120
% 0.86/1.03  prop_preprocess_simplified:             5454
% 0.86/1.03  prop_fo_subsumed:                       96
% 0.86/1.03  prop_solver_time:                       0.
% 0.86/1.03  smt_solver_time:                        0.
% 0.86/1.03  smt_fast_solver_time:                   0.
% 0.86/1.03  prop_fast_solver_time:                  0.
% 0.86/1.03  prop_unsat_core_time:                   0.
% 0.86/1.03  
% 0.86/1.03  ------ QBF
% 0.86/1.03  
% 0.86/1.03  qbf_q_res:                              0
% 0.86/1.03  qbf_num_tautologies:                    0
% 0.86/1.03  qbf_prep_cycles:                        0
% 0.86/1.03  
% 0.86/1.03  ------ BMC1
% 0.86/1.03  
% 0.86/1.03  bmc1_current_bound:                     -1
% 0.86/1.03  bmc1_last_solved_bound:                 -1
% 0.86/1.03  bmc1_unsat_core_size:                   -1
% 0.86/1.03  bmc1_unsat_core_parents_size:           -1
% 0.86/1.03  bmc1_merge_next_fun:                    0
% 0.86/1.03  bmc1_unsat_core_clauses_time:           0.
% 0.86/1.03  
% 0.86/1.03  ------ Instantiation
% 0.86/1.03  
% 0.86/1.03  inst_num_of_clauses:                    255
% 0.86/1.03  inst_num_in_passive:                    31
% 0.86/1.03  inst_num_in_active:                     187
% 0.86/1.03  inst_num_in_unprocessed:                37
% 0.86/1.03  inst_num_of_loops:                      210
% 0.86/1.03  inst_num_of_learning_restarts:          0
% 0.86/1.03  inst_num_moves_active_passive:          19
% 0.86/1.03  inst_lit_activity:                      0
% 0.86/1.03  inst_lit_activity_moves:                0
% 0.86/1.03  inst_num_tautologies:                   0
% 0.86/1.03  inst_num_prop_implied:                  0
% 0.86/1.03  inst_num_existing_simplified:           0
% 0.86/1.03  inst_num_eq_res_simplified:             0
% 0.86/1.03  inst_num_child_elim:                    0
% 0.86/1.03  inst_num_of_dismatching_blockings:      40
% 0.86/1.03  inst_num_of_non_proper_insts:           221
% 0.86/1.03  inst_num_of_duplicates:                 0
% 0.86/1.03  inst_inst_num_from_inst_to_res:         0
% 0.86/1.03  inst_dismatching_checking_time:         0.
% 0.86/1.03  
% 0.86/1.03  ------ Resolution
% 0.86/1.03  
% 0.86/1.03  res_num_of_clauses:                     0
% 0.86/1.03  res_num_in_passive:                     0
% 0.86/1.03  res_num_in_active:                      0
% 0.86/1.03  res_num_of_loops:                       177
% 0.86/1.03  res_forward_subset_subsumed:            49
% 0.86/1.03  res_backward_subset_subsumed:           0
% 0.86/1.03  res_forward_subsumed:                   0
% 0.86/1.03  res_backward_subsumed:                  0
% 0.86/1.03  res_forward_subsumption_resolution:     2
% 0.86/1.03  res_backward_subsumption_resolution:    0
% 0.86/1.03  res_clause_to_clause_subsumption:       182
% 0.86/1.03  res_orphan_elimination:                 0
% 0.86/1.03  res_tautology_del:                      25
% 0.86/1.03  res_num_eq_res_simplified:              0
% 0.86/1.03  res_num_sel_changes:                    0
% 0.86/1.03  res_moves_from_active_to_pass:          0
% 0.86/1.03  
% 0.86/1.03  ------ Superposition
% 0.86/1.03  
% 0.86/1.03  sup_time_total:                         0.
% 0.86/1.03  sup_time_generating:                    0.
% 0.86/1.03  sup_time_sim_full:                      0.
% 0.86/1.03  sup_time_sim_immed:                     0.
% 0.86/1.03  
% 0.86/1.03  sup_num_of_clauses:                     46
% 0.86/1.03  sup_num_in_active:                      39
% 0.86/1.03  sup_num_in_passive:                     7
% 0.86/1.03  sup_num_of_loops:                       40
% 0.86/1.03  sup_fw_superposition:                   18
% 0.86/1.03  sup_bw_superposition:                   6
% 0.86/1.03  sup_immediate_simplified:               7
% 0.86/1.03  sup_given_eliminated:                   0
% 0.86/1.03  comparisons_done:                       0
% 0.86/1.03  comparisons_avoided:                    0
% 0.86/1.03  
% 0.86/1.03  ------ Simplifications
% 0.86/1.03  
% 0.86/1.03  
% 0.86/1.03  sim_fw_subset_subsumed:                 0
% 0.86/1.03  sim_bw_subset_subsumed:                 2
% 0.86/1.03  sim_fw_subsumed:                        0
% 0.86/1.03  sim_bw_subsumed:                        0
% 0.86/1.03  sim_fw_subsumption_res:                 3
% 0.86/1.03  sim_bw_subsumption_res:                 0
% 0.86/1.03  sim_tautology_del:                      2
% 0.86/1.03  sim_eq_tautology_del:                   0
% 0.86/1.03  sim_eq_res_simp:                        0
% 0.86/1.03  sim_fw_demodulated:                     4
% 0.86/1.03  sim_bw_demodulated:                     1
% 0.86/1.03  sim_light_normalised:                   4
% 0.86/1.03  sim_joinable_taut:                      0
% 0.86/1.03  sim_joinable_simp:                      0
% 0.86/1.03  sim_ac_normalised:                      0
% 0.86/1.03  sim_smt_subsumption:                    0
% 0.86/1.03  
%------------------------------------------------------------------------------
