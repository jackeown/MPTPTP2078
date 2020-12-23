%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:58 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :  260 (2582 expanded)
%              Number of clauses        :  169 ( 572 expanded)
%              Number of leaves         :   20 ( 837 expanded)
%              Depth                    :   38
%              Number of atoms          : 1610 (36704 expanded)
%              Number of equality atoms :  236 (2526 expanded)
%              Maximal formula depth    :   27 (   7 average)
%              Maximal clause size      :   38 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X1,X4) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f6])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r2_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X1,sK0(X0,X1,X2))
        & r2_lattice3(X0,X2,sK0(X0,X1,X2))
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,X1,sK0(X0,X1,X2))
                  & r2_lattice3(X0,X2,sK0(X0,X1,X2))
                  & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f42])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X2) = X1
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f51,plain,(
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
     => ( k1_waybel_2(X0,sK5) != X1
        & r3_waybel_9(X0,sK5,X1)
        & v10_waybel_0(sK5,X0)
        & ! [X3] :
            ( v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & l1_waybel_0(sK5,X0)
        & v7_waybel_0(sK5)
        & v4_orders_2(sK5)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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
            ( k1_waybel_2(X0,X2) != sK4
            & r3_waybel_9(X0,X2,sK4)
            & v10_waybel_0(X2,X0)
            & ! [X3] :
                ( v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
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
              ( k1_waybel_2(sK3,X2) != X1
              & r3_waybel_9(sK3,X2,X1)
              & v10_waybel_0(X2,sK3)
              & ! [X3] :
                  ( v5_pre_topc(k4_waybel_1(sK3,X3),sK3,sK3)
                  | ~ m1_subset_1(X3,u1_struct_0(sK3)) )
              & l1_waybel_0(X2,sK3)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l1_waybel_9(sK3)
      & v1_compts_1(sK3)
      & v2_lattice3(sK3)
      & v1_lattice3(sK3)
      & v5_orders_2(sK3)
      & v4_orders_2(sK3)
      & v3_orders_2(sK3)
      & v8_pre_topc(sK3)
      & v2_pre_topc(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( k1_waybel_2(sK3,sK5) != sK4
    & r3_waybel_9(sK3,sK5,sK4)
    & v10_waybel_0(sK5,sK3)
    & ! [X3] :
        ( v5_pre_topc(k4_waybel_1(sK3,X3),sK3,sK3)
        | ~ m1_subset_1(X3,u1_struct_0(sK3)) )
    & l1_waybel_0(sK5,sK3)
    & v7_waybel_0(sK5)
    & v4_orders_2(sK5)
    & ~ v2_struct_0(sK5)
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_waybel_9(sK3)
    & v1_compts_1(sK3)
    & v2_lattice3(sK3)
    & v1_lattice3(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & v8_pre_topc(sK3)
    & v2_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f40,f51,f50,f49])).

fof(f80,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f84,plain,(
    l1_waybel_9(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => ( l1_orders_2(X0)
        & l1_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & l1_pre_topc(X0) )
      | ~ l1_waybel_9(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f71,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X2) = X1
      | r2_lattice3(X0,X2,sK0(X0,X1,X2))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f78,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f81,plain,(
    v1_lattice3(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f92,plain,(
    r3_waybel_9(sK3,sK5,sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f88,plain,(
    v7_waybel_0(sK5) ),
    inference(cnf_transformation,[],[f52])).

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
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) )
                      & X2 = X3 )
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
                         => r3_orders_2(X0,X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(rectify,[],[f12])).

fof(f37,plain,(
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

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f46,plain,(
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
    inference(rectify,[],[f38])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X5] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X5),X0,X0)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0)
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r3_orders_2(X0,X3,X4)
                      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r3_waybel_9(X0,X1,X2)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f46,f47])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r3_orders_2(X0,X3,X4)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
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
    inference(cnf_transformation,[],[f48])).

fof(f98,plain,(
    ! [X4,X0,X3,X1] :
      ( r3_orders_2(X0,X3,X4)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
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
    inference(equality_resolution,[],[f75])).

fof(f90,plain,(
    ! [X3] :
      ( v5_pre_topc(k4_waybel_1(sK3,X3),sK3,sK3)
      | ~ m1_subset_1(X3,u1_struct_0(sK3)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f76,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f77,plain,(
    v8_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f79,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f82,plain,(
    v2_lattice3(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f83,plain,(
    v1_compts_1(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f86,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f87,plain,(
    v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f89,plain,(
    l1_waybel_0(sK5,sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f85,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f52])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r3_orders_2(X0,X3,X4)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
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
    inference(cnf_transformation,[],[f48])).

fof(f99,plain,(
    ! [X4,X0,X3,X1] :
      ( r3_orders_2(X0,X3,X4)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
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
    inference(equality_resolution,[],[f74])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f70,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f55,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_yellow_0(X0,k2_relat_1(X1)) = k4_yellow_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_yellow_0(X0,k2_relat_1(X1)) = k4_yellow_2(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_yellow_0(X0,k2_relat_1(X1)) = k4_yellow_2(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_yellow_0(X0,k2_relat_1(X1)) = k4_yellow_2(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1))
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1))
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X2) = X1
      | ~ r1_orders_2(X0,X1,sK0(X0,X1,X2))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
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

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X4] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0)
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v10_waybel_0(X1,X0)
                  | ( ~ v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0)
                    & m1_subset_1(sK1(X0),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f44])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v10_waybel_0(X1,X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0)
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
    inference(cnf_transformation,[],[f45])).

fof(f96,plain,(
    ! [X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v10_waybel_0(X1,X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0)
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

fof(f91,plain,(
    v10_waybel_0(sK5,sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v10_waybel_0(X1,X0)
      | m1_subset_1(sK1(X0),u1_struct_0(X0))
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
    inference(cnf_transformation,[],[f45])).

fof(f97,plain,(
    ! [X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v10_waybel_0(X1,X0)
      | m1_subset_1(sK1(X0),u1_struct_0(X0))
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
    inference(equality_resolution,[],[f72])).

fof(f93,plain,(
    k1_waybel_2(sK3,sK5) != sK4 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_11,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_36,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1162,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X2,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_36])).

cnf(c_1163,plain,
    ( ~ r2_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK0(sK3,X1,X0),u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | k1_yellow_0(sK3,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1162])).

cnf(c_32,negated_conjecture,
    ( l1_waybel_9(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_17,plain,
    ( ~ l1_waybel_9(X0)
    | l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_76,plain,
    ( ~ l1_waybel_9(sK3)
    | l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1167,plain,
    ( m1_subset_1(sK0(sK3,X1,X0),u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r2_lattice3(sK3,X0,X1)
    | k1_yellow_0(sK3,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1163,c_32,c_76])).

cnf(c_1168,plain,
    ( ~ r2_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK0(sK3,X1,X0),u1_struct_0(sK3))
    | k1_yellow_0(sK3,X0) = X1 ),
    inference(renaming,[status(thm)],[c_1167])).

cnf(c_2261,plain,
    ( ~ r2_lattice3(sK3,X0_70,X0_68)
    | ~ m1_subset_1(X0_68,u1_struct_0(sK3))
    | m1_subset_1(sK0(sK3,X0_68,X0_70),u1_struct_0(sK3))
    | k1_yellow_0(sK3,X0_70) = X0_68 ),
    inference(subtyping,[status(esa)],[c_1168])).

cnf(c_2715,plain,
    ( k1_yellow_0(sK3,X0_70) = X0_68
    | r2_lattice3(sK3,X0_70,X0_68) != iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK0(sK3,X0_68,X0_70),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2261])).

cnf(c_10,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK0(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1186,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK0(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_36])).

cnf(c_1187,plain,
    ( ~ r2_lattice3(sK3,X0,X1)
    | r2_lattice3(sK3,X0,sK0(sK3,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | k1_yellow_0(sK3,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1186])).

cnf(c_1191,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_lattice3(sK3,X0,sK0(sK3,X1,X0))
    | ~ r2_lattice3(sK3,X0,X1)
    | k1_yellow_0(sK3,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1187,c_32,c_76])).

cnf(c_1192,plain,
    ( ~ r2_lattice3(sK3,X0,X1)
    | r2_lattice3(sK3,X0,sK0(sK3,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k1_yellow_0(sK3,X0) = X1 ),
    inference(renaming,[status(thm)],[c_1191])).

cnf(c_2260,plain,
    ( ~ r2_lattice3(sK3,X0_70,X0_68)
    | r2_lattice3(sK3,X0_70,sK0(sK3,X0_68,X0_70))
    | ~ m1_subset_1(X0_68,u1_struct_0(sK3))
    | k1_yellow_0(sK3,X0_70) = X0_68 ),
    inference(subtyping,[status(esa)],[c_1192])).

cnf(c_2716,plain,
    ( k1_yellow_0(sK3,X0_70) = X0_68
    | r2_lattice3(sK3,X0_70,X0_68) != iProver_top
    | r2_lattice3(sK3,X0_70,sK0(sK3,X0_68,X0_70)) = iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2260])).

cnf(c_4,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_38,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_723,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_38])).

cnf(c_724,plain,
    ( r1_orders_2(sK3,X0,X1)
    | ~ r3_orders_2(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_723])).

cnf(c_35,negated_conjecture,
    ( v1_lattice3(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_5,plain,
    ( ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_112,plain,
    ( ~ v1_lattice3(sK3)
    | ~ v2_struct_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_728,plain,
    ( r1_orders_2(sK3,X0,X1)
    | ~ r3_orders_2(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_724,c_35,c_32,c_76,c_112])).

cnf(c_729,plain,
    ( r1_orders_2(sK3,X0,X1)
    | ~ r3_orders_2(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_728])).

cnf(c_24,negated_conjecture,
    ( r3_waybel_9(sK3,sK5,sK4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_28,negated_conjecture,
    ( v7_waybel_0(sK5) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_21,plain,
    ( ~ v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0)
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
    inference(cnf_transformation,[],[f98])).

cnf(c_26,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(sK3,X0),sK3,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_557,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
    | r3_orders_2(X0,X2,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(sK3))
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
    | k4_waybel_1(X0,sK2(X0)) != k4_waybel_1(sK3,X4)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_26])).

cnf(c_558,plain,
    ( ~ r3_waybel_9(sK3,X0,X1)
    | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
    | r3_orders_2(sK3,X1,X2)
    | ~ l1_waybel_0(X0,sK3)
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ v2_pre_topc(sK3)
    | ~ v8_pre_topc(sK3)
    | ~ v2_lattice3(sK3)
    | ~ v1_compts_1(sK3)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK3)
    | ~ v7_waybel_0(X0)
    | ~ l1_waybel_9(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v1_lattice3(sK3)
    | v2_struct_0(X0)
    | ~ v3_orders_2(sK3)
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X3) ),
    inference(unflattening,[status(thm)],[c_557])).

cnf(c_40,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_39,negated_conjecture,
    ( v8_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_37,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_34,negated_conjecture,
    ( v2_lattice3(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_33,negated_conjecture,
    ( v1_compts_1(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_562,plain,
    ( v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ l1_waybel_0(X0,sK3)
    | r3_orders_2(sK3,X1,X2)
    | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
    | ~ r3_waybel_9(sK3,X0,X1)
    | ~ v7_waybel_0(X0)
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_558,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32])).

cnf(c_563,plain,
    ( ~ r3_waybel_9(sK3,X0,X1)
    | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
    | r3_orders_2(sK3,X1,X2)
    | ~ l1_waybel_0(X0,sK3)
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X3) ),
    inference(renaming,[status(thm)],[c_562])).

cnf(c_811,plain,
    ( ~ r3_waybel_9(sK3,X0,X1)
    | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
    | r3_orders_2(sK3,X1,X2)
    | ~ l1_waybel_0(X0,sK3)
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X3)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_563])).

cnf(c_812,plain,
    ( ~ r3_waybel_9(sK3,sK5,X0)
    | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
    | r3_orders_2(sK3,X0,X1)
    | ~ l1_waybel_0(sK5,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ v4_orders_2(sK5)
    | v2_struct_0(sK5)
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X2) ),
    inference(unflattening,[status(thm)],[c_811])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_29,negated_conjecture,
    ( v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_27,negated_conjecture,
    ( l1_waybel_0(sK5,sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_816,plain,
    ( r3_orders_2(sK3,X0,X1)
    | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
    | ~ r3_waybel_9(sK3,sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_812,c_30,c_29,c_27])).

cnf(c_817,plain,
    ( ~ r3_waybel_9(sK3,sK5,X0)
    | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
    | r3_orders_2(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X2) ),
    inference(renaming,[status(thm)],[c_816])).

cnf(c_947,plain,
    ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | r3_orders_2(sK3,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X2)
    | sK4 != X1
    | sK5 != sK5
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_817])).

cnf(c_948,plain,
    ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | r3_orders_2(sK3,sK4,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1) ),
    inference(unflattening,[status(thm)],[c_947])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_952,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r3_orders_2(sK3,sK4,X0)
    | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_948,c_31])).

cnf(c_953,plain,
    ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | r3_orders_2(sK3,sK4,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1) ),
    inference(renaming,[status(thm)],[c_952])).

cnf(c_1076,plain,
    ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | r1_orders_2(sK3,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | X0 != X2
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X3)
    | sK4 != X1
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_729,c_953])).

cnf(c_1077,plain,
    ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | r1_orders_2(sK3,sK4,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1) ),
    inference(unflattening,[status(thm)],[c_1076])).

cnf(c_1081,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r1_orders_2(sK3,sK4,X0)
    | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1077,c_31])).

cnf(c_1082,plain,
    ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | r1_orders_2(sK3,sK4,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1) ),
    inference(renaming,[status(thm)],[c_1081])).

cnf(c_2264,plain,
    ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_68)
    | r1_orders_2(sK3,sK4,X0_68)
    | ~ m1_subset_1(X1_68,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_68,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1_68) ),
    inference(subtyping,[status(esa)],[c_1082])).

cnf(c_2276,plain,
    ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_68)
    | r1_orders_2(sK3,sK4,X0_68)
    | ~ m1_subset_1(X0_68,u1_struct_0(sK3))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_2264])).

cnf(c_2711,plain,
    ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_68) != iProver_top
    | r1_orders_2(sK3,sK4,X0_68) = iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK3)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2276])).

cnf(c_22,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
    | r3_orders_2(X0,X2,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
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
    inference(cnf_transformation,[],[f99])).

cnf(c_633,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
    | r3_orders_2(X0,X2,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | m1_subset_1(sK2(X0),u1_struct_0(X0))
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
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_33])).

cnf(c_634,plain,
    ( ~ r3_waybel_9(sK3,X0,X1)
    | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
    | r3_orders_2(sK3,X1,X2)
    | ~ l1_waybel_0(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
    | ~ v2_pre_topc(sK3)
    | ~ v8_pre_topc(sK3)
    | ~ v2_lattice3(sK3)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK3)
    | ~ v7_waybel_0(X0)
    | ~ l1_waybel_9(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v1_lattice3(sK3)
    | v2_struct_0(X0)
    | ~ v3_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_633])).

cnf(c_638,plain,
    ( v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK3,X0,X1)
    | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
    | r3_orders_2(sK3,X1,X2)
    | ~ l1_waybel_0(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
    | ~ v7_waybel_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_634,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_32])).

cnf(c_639,plain,
    ( ~ r3_waybel_9(sK3,X0,X1)
    | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
    | r3_orders_2(sK3,X1,X2)
    | ~ l1_waybel_0(X0,sK3)
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_638])).

cnf(c_781,plain,
    ( ~ r3_waybel_9(sK3,X0,X1)
    | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
    | r3_orders_2(sK3,X1,X2)
    | ~ l1_waybel_0(X0,sK3)
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_639])).

cnf(c_782,plain,
    ( ~ r3_waybel_9(sK3,sK5,X0)
    | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
    | r3_orders_2(sK3,X0,X1)
    | ~ l1_waybel_0(sK5,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
    | ~ v4_orders_2(sK5)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_781])).

cnf(c_786,plain,
    ( r3_orders_2(sK3,X0,X1)
    | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
    | ~ r3_waybel_9(sK3,sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_782,c_30,c_29,c_27])).

cnf(c_787,plain,
    ( ~ r3_waybel_9(sK3,sK5,X0)
    | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
    | r3_orders_2(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_786])).

cnf(c_974,plain,
    ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | r3_orders_2(sK3,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
    | sK4 != X1
    | sK5 != sK5
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_787])).

cnf(c_975,plain,
    ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | r3_orders_2(sK3,sK4,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_974])).

cnf(c_979,plain,
    ( m1_subset_1(sK2(sK3),u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r3_orders_2(sK3,sK4,X0)
    | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_975,c_31])).

cnf(c_980,plain,
    ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | r3_orders_2(sK3,sK4,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_979])).

cnf(c_1052,plain,
    ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | r1_orders_2(sK3,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
    | X0 != X2
    | sK4 != X1
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_729,c_980])).

cnf(c_1053,plain,
    ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | r1_orders_2(sK3,sK4,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_1052])).

cnf(c_1057,plain,
    ( m1_subset_1(sK2(sK3),u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r1_orders_2(sK3,sK4,X0)
    | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1053,c_31])).

cnf(c_1058,plain,
    ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | r1_orders_2(sK3,sK4,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_1057])).

cnf(c_2265,plain,
    ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_68)
    | r1_orders_2(sK3,sK4,X0_68)
    | ~ m1_subset_1(X0_68,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1058])).

cnf(c_2343,plain,
    ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_68) != iProver_top
    | r1_orders_2(sK3,sK4,X0_68) = iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2265])).

cnf(c_2277,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_2264])).

cnf(c_2346,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2277])).

cnf(c_2347,plain,
    ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_68) != iProver_top
    | r1_orders_2(sK3,sK4,X0_68) = iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK3)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2276])).

cnf(c_2275,plain,
    ( ~ m1_subset_1(X0_68,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X0_68)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_2264])).

cnf(c_2712,plain,
    ( k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X0_68)
    | m1_subset_1(X0_68,u1_struct_0(sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2275])).

cnf(c_3501,plain,
    ( m1_subset_1(sK2(sK3),u1_struct_0(sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2712])).

cnf(c_3546,plain,
    ( m1_subset_1(X0_68,u1_struct_0(sK3)) != iProver_top
    | r1_orders_2(sK3,sK4,X0_68) = iProver_top
    | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_68) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2711,c_2343,c_2346,c_2347,c_3501])).

cnf(c_3547,plain,
    ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_68) != iProver_top
    | r1_orders_2(sK3,sK4,X0_68) = iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3546])).

cnf(c_14,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_18,plain,
    ( ~ l1_waybel_9(X0)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_444,plain,
    ( ~ l1_waybel_9(X0)
    | l1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_18,c_2])).

cnf(c_458,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_waybel_9(X2)
    | X2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_444])).

cnf(c_459,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_waybel_9(X1) ),
    inference(unflattening,[status(thm)],[c_458])).

cnf(c_699,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_459,c_32])).

cnf(c_700,plain,
    ( ~ l1_waybel_0(X0,sK3)
    | m1_subset_1(u1_waybel_0(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) ),
    inference(unflattening,[status(thm)],[c_699])).

cnf(c_867,plain,
    ( m1_subset_1(u1_waybel_0(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
    | sK5 != X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_700])).

cnf(c_868,plain,
    ( m1_subset_1(u1_waybel_0(sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(unflattening,[status(thm)],[c_867])).

cnf(c_2269,plain,
    ( m1_subset_1(u1_waybel_0(sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_868])).

cnf(c_2705,plain,
    ( m1_subset_1(u1_waybel_0(sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2269])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2273,plain,
    ( ~ m1_subset_1(X0_68,k1_zfmisc_1(k2_zfmisc_1(X0_71,X1_71)))
    | k2_relset_1(X0_71,X1_71,X0_68) = k2_relat_1(X0_68) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2703,plain,
    ( k2_relset_1(X0_71,X1_71,X0_68) = k2_relat_1(X0_68)
    | m1_subset_1(X0_68,k1_zfmisc_1(k2_zfmisc_1(X0_71,X1_71))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2273])).

cnf(c_2964,plain,
    ( k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)) = k2_relat_1(u1_waybel_0(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_2705,c_2703])).

cnf(c_3552,plain,
    ( r2_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_68) != iProver_top
    | r1_orders_2(sK3,sK4,X0_68) = iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3547,c_2964])).

cnf(c_3560,plain,
    ( k1_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = X0_68
    | r2_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_68) != iProver_top
    | r1_orders_2(sK3,sK4,sK0(sK3,X0_68,k2_relat_1(u1_waybel_0(sK3,sK5)))) = iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK0(sK3,X0_68,k2_relat_1(u1_waybel_0(sK3,sK5))),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2716,c_3552])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2274,plain,
    ( ~ m1_subset_1(X0_68,k1_zfmisc_1(k2_zfmisc_1(X0_71,X1_71)))
    | v1_relat_1(X0_68) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2702,plain,
    ( m1_subset_1(X0_68,k1_zfmisc_1(k2_zfmisc_1(X0_71,X1_71))) != iProver_top
    | v1_relat_1(X0_68) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2274])).

cnf(c_2959,plain,
    ( v1_relat_1(u1_waybel_0(sK3,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2705,c_2702])).

cnf(c_16,plain,
    ( v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_relat_1(X1)
    | k1_yellow_0(X0,k2_relat_1(X1)) = k4_yellow_2(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_686,plain,
    ( ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_35])).

cnf(c_687,plain,
    ( ~ v2_struct_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_686])).

cnf(c_689,plain,
    ( ~ v2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_687,c_35,c_32,c_76,c_112])).

cnf(c_892,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_relat_1(X1)
    | k1_yellow_0(X0,k2_relat_1(X1)) = k4_yellow_2(X0,X1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_689])).

cnf(c_893,plain,
    ( ~ l1_orders_2(sK3)
    | ~ v1_relat_1(X0)
    | k1_yellow_0(sK3,k2_relat_1(X0)) = k4_yellow_2(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_892])).

cnf(c_897,plain,
    ( ~ v1_relat_1(X0)
    | k1_yellow_0(sK3,k2_relat_1(X0)) = k4_yellow_2(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_893,c_32,c_76])).

cnf(c_2268,plain,
    ( ~ v1_relat_1(X0_68)
    | k1_yellow_0(sK3,k2_relat_1(X0_68)) = k4_yellow_2(sK3,X0_68) ),
    inference(subtyping,[status(esa)],[c_897])).

cnf(c_2706,plain,
    ( k1_yellow_0(sK3,k2_relat_1(X0_68)) = k4_yellow_2(sK3,X0_68)
    | v1_relat_1(X0_68) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2268])).

cnf(c_3227,plain,
    ( k1_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = k4_yellow_2(sK3,u1_waybel_0(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_2959,c_2706])).

cnf(c_15,plain,
    ( ~ l1_waybel_0(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | k4_yellow_2(X1,u1_waybel_0(X1,X0)) = k1_waybel_2(X1,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_859,plain,
    ( v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k4_yellow_2(X0,u1_waybel_0(X0,X1)) = k1_waybel_2(X0,X1)
    | sK5 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_27])).

cnf(c_860,plain,
    ( v2_struct_0(sK3)
    | ~ l1_orders_2(sK3)
    | k4_yellow_2(sK3,u1_waybel_0(sK3,sK5)) = k1_waybel_2(sK3,sK5) ),
    inference(unflattening,[status(thm)],[c_859])).

cnf(c_862,plain,
    ( k4_yellow_2(sK3,u1_waybel_0(sK3,sK5)) = k1_waybel_2(sK3,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_860,c_35,c_32,c_76,c_112])).

cnf(c_2270,plain,
    ( k4_yellow_2(sK3,u1_waybel_0(sK3,sK5)) = k1_waybel_2(sK3,sK5) ),
    inference(subtyping,[status(esa)],[c_862])).

cnf(c_3228,plain,
    ( k1_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = k1_waybel_2(sK3,sK5) ),
    inference(light_normalisation,[status(thm)],[c_3227,c_2270])).

cnf(c_3578,plain,
    ( k1_waybel_2(sK3,sK5) = X0_68
    | r2_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_68) != iProver_top
    | r1_orders_2(sK3,sK4,sK0(sK3,X0_68,k2_relat_1(u1_waybel_0(sK3,sK5)))) = iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK0(sK3,X0_68,k2_relat_1(u1_waybel_0(sK3,sK5))),u1_struct_0(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3560,c_3228])).

cnf(c_3828,plain,
    ( k1_waybel_2(sK3,sK5) = X0_68
    | k1_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = X0_68
    | r2_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_68) != iProver_top
    | r1_orders_2(sK3,sK4,sK0(sK3,X0_68,k2_relat_1(u1_waybel_0(sK3,sK5)))) = iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2715,c_3578])).

cnf(c_3834,plain,
    ( k1_waybel_2(sK3,sK5) = X0_68
    | r2_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_68) != iProver_top
    | r1_orders_2(sK3,sK4,sK0(sK3,X0_68,k2_relat_1(u1_waybel_0(sK3,sK5)))) = iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3828,c_3228])).

cnf(c_9,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1210,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_36])).

cnf(c_1211,plain,
    ( ~ r2_lattice3(sK3,X0,X1)
    | ~ r1_orders_2(sK3,X1,sK0(sK3,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | k1_yellow_0(sK3,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1210])).

cnf(c_1215,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r1_orders_2(sK3,X1,sK0(sK3,X1,X0))
    | ~ r2_lattice3(sK3,X0,X1)
    | k1_yellow_0(sK3,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1211,c_32,c_76])).

cnf(c_1216,plain,
    ( ~ r2_lattice3(sK3,X0,X1)
    | ~ r1_orders_2(sK3,X1,sK0(sK3,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k1_yellow_0(sK3,X0) = X1 ),
    inference(renaming,[status(thm)],[c_1215])).

cnf(c_2259,plain,
    ( ~ r2_lattice3(sK3,X0_70,X0_68)
    | ~ r1_orders_2(sK3,X0_68,sK0(sK3,X0_68,X0_70))
    | ~ m1_subset_1(X0_68,u1_struct_0(sK3))
    | k1_yellow_0(sK3,X0_70) = X0_68 ),
    inference(subtyping,[status(esa)],[c_1216])).

cnf(c_2717,plain,
    ( k1_yellow_0(sK3,X0_70) = X0_68
    | r2_lattice3(sK3,X0_70,X0_68) != iProver_top
    | r1_orders_2(sK3,X0_68,sK0(sK3,X0_68,X0_70)) != iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2259])).

cnf(c_3848,plain,
    ( k1_waybel_2(sK3,sK5) = sK4
    | k1_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = sK4
    | r2_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),sK4) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3834,c_2717])).

cnf(c_3853,plain,
    ( k1_waybel_2(sK3,sK5) = sK4
    | r2_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),sK4) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3848,c_3228])).

cnf(c_19,plain,
    ( ~ v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0)
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
    inference(cnf_transformation,[],[f96])).

cnf(c_25,negated_conjecture,
    ( v10_waybel_0(sK5,sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_523,plain,
    ( ~ v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0)
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
    | sK5 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_25])).

cnf(c_524,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK3,sK1(sK3)),sK3,sK3)
    | ~ r3_waybel_9(sK3,sK5,X0)
    | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | ~ l1_waybel_0(sK5,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ v2_pre_topc(sK3)
    | ~ v8_pre_topc(sK3)
    | ~ v2_lattice3(sK3)
    | ~ v1_compts_1(sK3)
    | ~ v4_orders_2(sK5)
    | ~ v4_orders_2(sK3)
    | ~ v7_waybel_0(sK5)
    | ~ l1_waybel_9(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v1_lattice3(sK3)
    | v2_struct_0(sK5)
    | ~ v3_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_523])).

cnf(c_528,plain,
    ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | ~ r3_waybel_9(sK3,sK5,X0)
    | ~ v5_pre_topc(k4_waybel_1(sK3,sK1(sK3)),sK3,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_524,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_30,c_29,c_28,c_27])).

cnf(c_529,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK3,sK1(sK3)),sK3,sK3)
    | ~ r3_waybel_9(sK3,sK5,X0)
    | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_528])).

cnf(c_602,plain,
    ( ~ r3_waybel_9(sK3,sK5,X0)
    | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X1)
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_529])).

cnf(c_998,plain,
    ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X1)
    | sK4 != X0
    | sK5 != sK5
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_602])).

cnf(c_999,plain,
    ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_998])).

cnf(c_1003,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
    | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_999,c_31])).

cnf(c_1004,plain,
    ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0) ),
    inference(renaming,[status(thm)],[c_1003])).

cnf(c_2267,plain,
    ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
    | ~ m1_subset_1(X0_68,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0_68) ),
    inference(subtyping,[status(esa)],[c_1004])).

cnf(c_2707,plain,
    ( k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0_68)
    | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) = iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2267])).

cnf(c_20,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
    | ~ v10_waybel_0(X1,X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0),u1_struct_0(X0))
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
    inference(cnf_transformation,[],[f97])).

cnf(c_499,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0),u1_struct_0(X0))
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
    | sK5 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_25])).

cnf(c_500,plain,
    ( ~ r3_waybel_9(sK3,sK5,X0)
    | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | ~ l1_waybel_0(sK5,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3),u1_struct_0(sK3))
    | ~ v2_pre_topc(sK3)
    | ~ v8_pre_topc(sK3)
    | ~ v2_lattice3(sK3)
    | ~ v1_compts_1(sK3)
    | ~ v4_orders_2(sK5)
    | ~ v4_orders_2(sK3)
    | ~ v7_waybel_0(sK5)
    | ~ l1_waybel_9(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v1_lattice3(sK3)
    | v2_struct_0(sK5)
    | ~ v3_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_499])).

cnf(c_504,plain,
    ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | ~ r3_waybel_9(sK3,sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_500,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_30,c_29,c_28,c_27])).

cnf(c_505,plain,
    ( ~ r3_waybel_9(sK3,sK5,X0)
    | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_504])).

cnf(c_1019,plain,
    ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3),u1_struct_0(sK3))
    | sK4 != X0
    | sK5 != sK5
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_505])).

cnf(c_1020,plain,
    ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
    | m1_subset_1(sK1(sK3),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_1019])).

cnf(c_1022,plain,
    ( m1_subset_1(sK1(sK3),u1_struct_0(sK3))
    | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1020,c_31])).

cnf(c_1023,plain,
    ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
    | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_1022])).

cnf(c_1024,plain,
    ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) = iProver_top
    | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1023])).

cnf(c_2283,plain,
    ( X0_72 = X0_72 ),
    theory(equality)).

cnf(c_2898,plain,
    ( k4_waybel_1(sK3,sK1(sK3)) = k4_waybel_1(sK3,sK1(sK3)) ),
    inference(instantiation,[status(thm)],[c_2283])).

cnf(c_2899,plain,
    ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
    | ~ m1_subset_1(sK1(sK3),u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,sK1(sK3)) ),
    inference(instantiation,[status(thm)],[c_2267])).

cnf(c_2900,plain,
    ( k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,sK1(sK3))
    | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) = iProver_top
    | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2899])).

cnf(c_2910,plain,
    ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2707,c_1024,c_2898,c_2900])).

cnf(c_3017,plain,
    ( r2_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2964,c_2910])).

cnf(c_23,negated_conjecture,
    ( k1_waybel_2(sK3,sK5) != sK4 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2272,negated_conjecture,
    ( k1_waybel_2(sK3,sK5) != sK4 ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_50,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3853,c_3017,c_2272,c_50])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:45:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 1.87/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.03  
% 1.87/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.87/1.03  
% 1.87/1.03  ------  iProver source info
% 1.87/1.03  
% 1.87/1.03  git: date: 2020-06-30 10:37:57 +0100
% 1.87/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.87/1.03  git: non_committed_changes: false
% 1.87/1.03  git: last_make_outside_of_git: false
% 1.87/1.03  
% 1.87/1.03  ------ 
% 1.87/1.03  
% 1.87/1.03  ------ Input Options
% 1.87/1.03  
% 1.87/1.03  --out_options                           all
% 1.87/1.03  --tptp_safe_out                         true
% 1.87/1.03  --problem_path                          ""
% 1.87/1.03  --include_path                          ""
% 1.87/1.03  --clausifier                            res/vclausify_rel
% 1.87/1.03  --clausifier_options                    --mode clausify
% 1.87/1.03  --stdin                                 false
% 1.87/1.03  --stats_out                             all
% 1.87/1.03  
% 1.87/1.03  ------ General Options
% 1.87/1.03  
% 1.87/1.03  --fof                                   false
% 1.87/1.03  --time_out_real                         305.
% 1.87/1.03  --time_out_virtual                      -1.
% 1.87/1.03  --symbol_type_check                     false
% 1.87/1.03  --clausify_out                          false
% 1.87/1.03  --sig_cnt_out                           false
% 1.87/1.03  --trig_cnt_out                          false
% 1.87/1.03  --trig_cnt_out_tolerance                1.
% 1.87/1.03  --trig_cnt_out_sk_spl                   false
% 1.87/1.03  --abstr_cl_out                          false
% 1.87/1.03  
% 1.87/1.03  ------ Global Options
% 1.87/1.03  
% 1.87/1.03  --schedule                              default
% 1.87/1.03  --add_important_lit                     false
% 1.87/1.03  --prop_solver_per_cl                    1000
% 1.87/1.03  --min_unsat_core                        false
% 1.87/1.03  --soft_assumptions                      false
% 1.87/1.03  --soft_lemma_size                       3
% 1.87/1.03  --prop_impl_unit_size                   0
% 1.87/1.03  --prop_impl_unit                        []
% 1.87/1.03  --share_sel_clauses                     true
% 1.87/1.03  --reset_solvers                         false
% 1.87/1.03  --bc_imp_inh                            [conj_cone]
% 1.87/1.03  --conj_cone_tolerance                   3.
% 1.87/1.03  --extra_neg_conj                        none
% 1.87/1.03  --large_theory_mode                     true
% 1.87/1.03  --prolific_symb_bound                   200
% 1.87/1.03  --lt_threshold                          2000
% 1.87/1.03  --clause_weak_htbl                      true
% 1.87/1.03  --gc_record_bc_elim                     false
% 1.87/1.03  
% 1.87/1.03  ------ Preprocessing Options
% 1.87/1.03  
% 1.87/1.03  --preprocessing_flag                    true
% 1.87/1.03  --time_out_prep_mult                    0.1
% 1.87/1.03  --splitting_mode                        input
% 1.87/1.03  --splitting_grd                         true
% 1.87/1.03  --splitting_cvd                         false
% 1.87/1.03  --splitting_cvd_svl                     false
% 1.87/1.03  --splitting_nvd                         32
% 1.87/1.03  --sub_typing                            true
% 1.87/1.03  --prep_gs_sim                           true
% 1.87/1.03  --prep_unflatten                        true
% 1.87/1.03  --prep_res_sim                          true
% 1.87/1.03  --prep_upred                            true
% 1.87/1.03  --prep_sem_filter                       exhaustive
% 1.87/1.03  --prep_sem_filter_out                   false
% 1.87/1.03  --pred_elim                             true
% 1.87/1.03  --res_sim_input                         true
% 1.87/1.03  --eq_ax_congr_red                       true
% 1.87/1.03  --pure_diseq_elim                       true
% 1.87/1.03  --brand_transform                       false
% 1.87/1.03  --non_eq_to_eq                          false
% 1.87/1.03  --prep_def_merge                        true
% 1.87/1.03  --prep_def_merge_prop_impl              false
% 1.87/1.03  --prep_def_merge_mbd                    true
% 1.87/1.03  --prep_def_merge_tr_red                 false
% 1.87/1.03  --prep_def_merge_tr_cl                  false
% 1.87/1.03  --smt_preprocessing                     true
% 1.87/1.03  --smt_ac_axioms                         fast
% 1.87/1.03  --preprocessed_out                      false
% 1.87/1.03  --preprocessed_stats                    false
% 1.87/1.03  
% 1.87/1.03  ------ Abstraction refinement Options
% 1.87/1.03  
% 1.87/1.03  --abstr_ref                             []
% 1.87/1.03  --abstr_ref_prep                        false
% 1.87/1.03  --abstr_ref_until_sat                   false
% 1.87/1.03  --abstr_ref_sig_restrict                funpre
% 1.87/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.87/1.03  --abstr_ref_under                       []
% 1.87/1.03  
% 1.87/1.03  ------ SAT Options
% 1.87/1.03  
% 1.87/1.03  --sat_mode                              false
% 1.87/1.03  --sat_fm_restart_options                ""
% 1.87/1.03  --sat_gr_def                            false
% 1.87/1.03  --sat_epr_types                         true
% 1.87/1.03  --sat_non_cyclic_types                  false
% 1.87/1.03  --sat_finite_models                     false
% 1.87/1.03  --sat_fm_lemmas                         false
% 1.87/1.03  --sat_fm_prep                           false
% 1.87/1.03  --sat_fm_uc_incr                        true
% 1.87/1.03  --sat_out_model                         small
% 1.87/1.03  --sat_out_clauses                       false
% 1.87/1.03  
% 1.87/1.03  ------ QBF Options
% 1.87/1.03  
% 1.87/1.03  --qbf_mode                              false
% 1.87/1.03  --qbf_elim_univ                         false
% 1.87/1.03  --qbf_dom_inst                          none
% 1.87/1.03  --qbf_dom_pre_inst                      false
% 1.87/1.03  --qbf_sk_in                             false
% 1.87/1.03  --qbf_pred_elim                         true
% 1.87/1.03  --qbf_split                             512
% 1.87/1.03  
% 1.87/1.03  ------ BMC1 Options
% 1.87/1.03  
% 1.87/1.03  --bmc1_incremental                      false
% 1.87/1.03  --bmc1_axioms                           reachable_all
% 1.87/1.03  --bmc1_min_bound                        0
% 1.87/1.03  --bmc1_max_bound                        -1
% 1.87/1.03  --bmc1_max_bound_default                -1
% 1.87/1.03  --bmc1_symbol_reachability              true
% 1.87/1.03  --bmc1_property_lemmas                  false
% 1.87/1.03  --bmc1_k_induction                      false
% 1.87/1.03  --bmc1_non_equiv_states                 false
% 1.87/1.03  --bmc1_deadlock                         false
% 1.87/1.03  --bmc1_ucm                              false
% 1.87/1.03  --bmc1_add_unsat_core                   none
% 1.87/1.03  --bmc1_unsat_core_children              false
% 1.87/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.87/1.03  --bmc1_out_stat                         full
% 1.87/1.03  --bmc1_ground_init                      false
% 1.87/1.03  --bmc1_pre_inst_next_state              false
% 1.87/1.03  --bmc1_pre_inst_state                   false
% 1.87/1.03  --bmc1_pre_inst_reach_state             false
% 1.87/1.03  --bmc1_out_unsat_core                   false
% 1.87/1.03  --bmc1_aig_witness_out                  false
% 1.87/1.03  --bmc1_verbose                          false
% 1.87/1.03  --bmc1_dump_clauses_tptp                false
% 1.87/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.87/1.03  --bmc1_dump_file                        -
% 1.87/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.87/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.87/1.03  --bmc1_ucm_extend_mode                  1
% 1.87/1.03  --bmc1_ucm_init_mode                    2
% 1.87/1.03  --bmc1_ucm_cone_mode                    none
% 1.87/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.87/1.03  --bmc1_ucm_relax_model                  4
% 1.87/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.87/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.87/1.03  --bmc1_ucm_layered_model                none
% 1.87/1.03  --bmc1_ucm_max_lemma_size               10
% 1.87/1.03  
% 1.87/1.03  ------ AIG Options
% 1.87/1.03  
% 1.87/1.03  --aig_mode                              false
% 1.87/1.03  
% 1.87/1.03  ------ Instantiation Options
% 1.87/1.03  
% 1.87/1.03  --instantiation_flag                    true
% 1.87/1.03  --inst_sos_flag                         false
% 1.87/1.03  --inst_sos_phase                        true
% 1.87/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.87/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.87/1.03  --inst_lit_sel_side                     num_symb
% 1.87/1.03  --inst_solver_per_active                1400
% 1.87/1.03  --inst_solver_calls_frac                1.
% 1.87/1.03  --inst_passive_queue_type               priority_queues
% 1.87/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.87/1.03  --inst_passive_queues_freq              [25;2]
% 1.87/1.03  --inst_dismatching                      true
% 1.87/1.03  --inst_eager_unprocessed_to_passive     true
% 1.87/1.03  --inst_prop_sim_given                   true
% 1.87/1.03  --inst_prop_sim_new                     false
% 1.87/1.03  --inst_subs_new                         false
% 1.87/1.03  --inst_eq_res_simp                      false
% 1.87/1.03  --inst_subs_given                       false
% 1.87/1.03  --inst_orphan_elimination               true
% 1.87/1.03  --inst_learning_loop_flag               true
% 1.87/1.03  --inst_learning_start                   3000
% 1.87/1.03  --inst_learning_factor                  2
% 1.87/1.03  --inst_start_prop_sim_after_learn       3
% 1.87/1.03  --inst_sel_renew                        solver
% 1.87/1.03  --inst_lit_activity_flag                true
% 1.87/1.03  --inst_restr_to_given                   false
% 1.87/1.03  --inst_activity_threshold               500
% 1.87/1.03  --inst_out_proof                        true
% 1.87/1.03  
% 1.87/1.03  ------ Resolution Options
% 1.87/1.03  
% 1.87/1.03  --resolution_flag                       true
% 1.87/1.03  --res_lit_sel                           adaptive
% 1.87/1.03  --res_lit_sel_side                      none
% 1.87/1.03  --res_ordering                          kbo
% 1.87/1.03  --res_to_prop_solver                    active
% 1.87/1.03  --res_prop_simpl_new                    false
% 1.87/1.03  --res_prop_simpl_given                  true
% 1.87/1.03  --res_passive_queue_type                priority_queues
% 1.87/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.87/1.03  --res_passive_queues_freq               [15;5]
% 1.87/1.03  --res_forward_subs                      full
% 1.87/1.03  --res_backward_subs                     full
% 1.87/1.03  --res_forward_subs_resolution           true
% 1.87/1.03  --res_backward_subs_resolution          true
% 1.87/1.03  --res_orphan_elimination                true
% 1.87/1.03  --res_time_limit                        2.
% 1.87/1.03  --res_out_proof                         true
% 1.87/1.03  
% 1.87/1.03  ------ Superposition Options
% 1.87/1.03  
% 1.87/1.03  --superposition_flag                    true
% 1.87/1.03  --sup_passive_queue_type                priority_queues
% 1.87/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.87/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.87/1.03  --demod_completeness_check              fast
% 1.87/1.03  --demod_use_ground                      true
% 1.87/1.03  --sup_to_prop_solver                    passive
% 1.87/1.03  --sup_prop_simpl_new                    true
% 1.87/1.03  --sup_prop_simpl_given                  true
% 1.87/1.03  --sup_fun_splitting                     false
% 1.87/1.03  --sup_smt_interval                      50000
% 1.87/1.03  
% 1.87/1.03  ------ Superposition Simplification Setup
% 1.87/1.03  
% 1.87/1.03  --sup_indices_passive                   []
% 1.87/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.87/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/1.03  --sup_full_bw                           [BwDemod]
% 1.87/1.03  --sup_immed_triv                        [TrivRules]
% 1.87/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.87/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/1.03  --sup_immed_bw_main                     []
% 1.87/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.87/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.87/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.87/1.03  
% 1.87/1.03  ------ Combination Options
% 1.87/1.03  
% 1.87/1.03  --comb_res_mult                         3
% 1.87/1.03  --comb_sup_mult                         2
% 1.87/1.03  --comb_inst_mult                        10
% 1.87/1.03  
% 1.87/1.03  ------ Debug Options
% 1.87/1.03  
% 1.87/1.03  --dbg_backtrace                         false
% 1.87/1.03  --dbg_dump_prop_clauses                 false
% 1.87/1.03  --dbg_dump_prop_clauses_file            -
% 1.87/1.03  --dbg_out_stat                          false
% 1.87/1.03  ------ Parsing...
% 1.87/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.87/1.03  
% 1.87/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe:16:0s pe_e  sf_s  rm: 16 0s  sf_e  pe_s  pe_e 
% 1.87/1.03  
% 1.87/1.03  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.87/1.03  
% 1.87/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.87/1.03  ------ Proving...
% 1.87/1.03  ------ Problem Properties 
% 1.87/1.03  
% 1.87/1.03  
% 1.87/1.03  clauses                                 22
% 1.87/1.03  conjectures                             2
% 1.87/1.03  EPR                                     1
% 1.87/1.03  Horn                                    15
% 1.87/1.03  unary                                   4
% 1.87/1.03  binary                                  5
% 1.87/1.03  lits                                    63
% 1.87/1.03  lits eq                                 11
% 1.87/1.03  fd_pure                                 0
% 1.87/1.03  fd_pseudo                               0
% 1.87/1.03  fd_cond                                 0
% 1.87/1.03  fd_pseudo_cond                          3
% 1.87/1.03  AC symbols                              0
% 1.87/1.03  
% 1.87/1.03  ------ Schedule dynamic 5 is on 
% 1.87/1.03  
% 1.87/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.87/1.03  
% 1.87/1.03  
% 1.87/1.03  ------ 
% 1.87/1.03  Current options:
% 1.87/1.03  ------ 
% 1.87/1.03  
% 1.87/1.03  ------ Input Options
% 1.87/1.03  
% 1.87/1.03  --out_options                           all
% 1.87/1.03  --tptp_safe_out                         true
% 1.87/1.03  --problem_path                          ""
% 1.87/1.03  --include_path                          ""
% 1.87/1.03  --clausifier                            res/vclausify_rel
% 1.87/1.03  --clausifier_options                    --mode clausify
% 1.87/1.03  --stdin                                 false
% 1.87/1.03  --stats_out                             all
% 1.87/1.03  
% 1.87/1.03  ------ General Options
% 1.87/1.03  
% 1.87/1.03  --fof                                   false
% 1.87/1.03  --time_out_real                         305.
% 1.87/1.03  --time_out_virtual                      -1.
% 1.87/1.03  --symbol_type_check                     false
% 1.87/1.03  --clausify_out                          false
% 1.87/1.03  --sig_cnt_out                           false
% 1.87/1.03  --trig_cnt_out                          false
% 1.87/1.03  --trig_cnt_out_tolerance                1.
% 1.87/1.03  --trig_cnt_out_sk_spl                   false
% 1.87/1.03  --abstr_cl_out                          false
% 1.87/1.03  
% 1.87/1.03  ------ Global Options
% 1.87/1.03  
% 1.87/1.03  --schedule                              default
% 1.87/1.03  --add_important_lit                     false
% 1.87/1.03  --prop_solver_per_cl                    1000
% 1.87/1.03  --min_unsat_core                        false
% 1.87/1.03  --soft_assumptions                      false
% 1.87/1.03  --soft_lemma_size                       3
% 1.87/1.03  --prop_impl_unit_size                   0
% 1.87/1.03  --prop_impl_unit                        []
% 1.87/1.03  --share_sel_clauses                     true
% 1.87/1.03  --reset_solvers                         false
% 1.87/1.03  --bc_imp_inh                            [conj_cone]
% 1.87/1.03  --conj_cone_tolerance                   3.
% 1.87/1.03  --extra_neg_conj                        none
% 1.87/1.03  --large_theory_mode                     true
% 1.87/1.03  --prolific_symb_bound                   200
% 1.87/1.03  --lt_threshold                          2000
% 1.87/1.03  --clause_weak_htbl                      true
% 1.87/1.03  --gc_record_bc_elim                     false
% 1.87/1.03  
% 1.87/1.03  ------ Preprocessing Options
% 1.87/1.03  
% 1.87/1.03  --preprocessing_flag                    true
% 1.87/1.03  --time_out_prep_mult                    0.1
% 1.87/1.03  --splitting_mode                        input
% 1.87/1.03  --splitting_grd                         true
% 1.87/1.03  --splitting_cvd                         false
% 1.87/1.03  --splitting_cvd_svl                     false
% 1.87/1.03  --splitting_nvd                         32
% 1.87/1.03  --sub_typing                            true
% 1.87/1.03  --prep_gs_sim                           true
% 1.87/1.03  --prep_unflatten                        true
% 1.87/1.03  --prep_res_sim                          true
% 1.87/1.03  --prep_upred                            true
% 1.87/1.03  --prep_sem_filter                       exhaustive
% 1.87/1.03  --prep_sem_filter_out                   false
% 1.87/1.03  --pred_elim                             true
% 1.87/1.03  --res_sim_input                         true
% 1.87/1.03  --eq_ax_congr_red                       true
% 1.87/1.03  --pure_diseq_elim                       true
% 1.87/1.03  --brand_transform                       false
% 1.87/1.03  --non_eq_to_eq                          false
% 1.87/1.03  --prep_def_merge                        true
% 1.87/1.03  --prep_def_merge_prop_impl              false
% 1.87/1.03  --prep_def_merge_mbd                    true
% 1.87/1.03  --prep_def_merge_tr_red                 false
% 1.87/1.03  --prep_def_merge_tr_cl                  false
% 1.87/1.03  --smt_preprocessing                     true
% 1.87/1.03  --smt_ac_axioms                         fast
% 1.87/1.03  --preprocessed_out                      false
% 1.87/1.03  --preprocessed_stats                    false
% 1.87/1.03  
% 1.87/1.03  ------ Abstraction refinement Options
% 1.87/1.03  
% 1.87/1.03  --abstr_ref                             []
% 1.87/1.03  --abstr_ref_prep                        false
% 1.87/1.03  --abstr_ref_until_sat                   false
% 1.87/1.03  --abstr_ref_sig_restrict                funpre
% 1.87/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.87/1.03  --abstr_ref_under                       []
% 1.87/1.03  
% 1.87/1.03  ------ SAT Options
% 1.87/1.03  
% 1.87/1.03  --sat_mode                              false
% 1.87/1.03  --sat_fm_restart_options                ""
% 1.87/1.03  --sat_gr_def                            false
% 1.87/1.03  --sat_epr_types                         true
% 1.87/1.03  --sat_non_cyclic_types                  false
% 1.87/1.03  --sat_finite_models                     false
% 1.87/1.03  --sat_fm_lemmas                         false
% 1.87/1.03  --sat_fm_prep                           false
% 1.87/1.03  --sat_fm_uc_incr                        true
% 1.87/1.03  --sat_out_model                         small
% 1.87/1.03  --sat_out_clauses                       false
% 1.87/1.03  
% 1.87/1.03  ------ QBF Options
% 1.87/1.03  
% 1.87/1.03  --qbf_mode                              false
% 1.87/1.03  --qbf_elim_univ                         false
% 1.87/1.03  --qbf_dom_inst                          none
% 1.87/1.03  --qbf_dom_pre_inst                      false
% 1.87/1.03  --qbf_sk_in                             false
% 1.87/1.03  --qbf_pred_elim                         true
% 1.87/1.03  --qbf_split                             512
% 1.87/1.03  
% 1.87/1.03  ------ BMC1 Options
% 1.87/1.03  
% 1.87/1.03  --bmc1_incremental                      false
% 1.87/1.03  --bmc1_axioms                           reachable_all
% 1.87/1.03  --bmc1_min_bound                        0
% 1.87/1.03  --bmc1_max_bound                        -1
% 1.87/1.03  --bmc1_max_bound_default                -1
% 1.87/1.03  --bmc1_symbol_reachability              true
% 1.87/1.03  --bmc1_property_lemmas                  false
% 1.87/1.03  --bmc1_k_induction                      false
% 1.87/1.03  --bmc1_non_equiv_states                 false
% 1.87/1.03  --bmc1_deadlock                         false
% 1.87/1.03  --bmc1_ucm                              false
% 1.87/1.03  --bmc1_add_unsat_core                   none
% 1.87/1.03  --bmc1_unsat_core_children              false
% 1.87/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.87/1.03  --bmc1_out_stat                         full
% 1.87/1.03  --bmc1_ground_init                      false
% 1.87/1.03  --bmc1_pre_inst_next_state              false
% 1.87/1.03  --bmc1_pre_inst_state                   false
% 1.87/1.03  --bmc1_pre_inst_reach_state             false
% 1.87/1.03  --bmc1_out_unsat_core                   false
% 1.87/1.03  --bmc1_aig_witness_out                  false
% 1.87/1.03  --bmc1_verbose                          false
% 1.87/1.03  --bmc1_dump_clauses_tptp                false
% 1.87/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.87/1.03  --bmc1_dump_file                        -
% 1.87/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.87/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.87/1.03  --bmc1_ucm_extend_mode                  1
% 1.87/1.03  --bmc1_ucm_init_mode                    2
% 1.87/1.03  --bmc1_ucm_cone_mode                    none
% 1.87/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.87/1.03  --bmc1_ucm_relax_model                  4
% 1.87/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.87/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.87/1.03  --bmc1_ucm_layered_model                none
% 1.87/1.03  --bmc1_ucm_max_lemma_size               10
% 1.87/1.03  
% 1.87/1.03  ------ AIG Options
% 1.87/1.03  
% 1.87/1.03  --aig_mode                              false
% 1.87/1.03  
% 1.87/1.03  ------ Instantiation Options
% 1.87/1.03  
% 1.87/1.03  --instantiation_flag                    true
% 1.87/1.03  --inst_sos_flag                         false
% 1.87/1.03  --inst_sos_phase                        true
% 1.87/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.87/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.87/1.03  --inst_lit_sel_side                     none
% 1.87/1.03  --inst_solver_per_active                1400
% 1.87/1.03  --inst_solver_calls_frac                1.
% 1.87/1.03  --inst_passive_queue_type               priority_queues
% 1.87/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.87/1.03  --inst_passive_queues_freq              [25;2]
% 1.87/1.03  --inst_dismatching                      true
% 1.87/1.03  --inst_eager_unprocessed_to_passive     true
% 1.87/1.03  --inst_prop_sim_given                   true
% 1.87/1.03  --inst_prop_sim_new                     false
% 1.87/1.03  --inst_subs_new                         false
% 1.87/1.03  --inst_eq_res_simp                      false
% 1.87/1.03  --inst_subs_given                       false
% 1.87/1.03  --inst_orphan_elimination               true
% 1.87/1.03  --inst_learning_loop_flag               true
% 1.87/1.03  --inst_learning_start                   3000
% 1.87/1.03  --inst_learning_factor                  2
% 1.87/1.03  --inst_start_prop_sim_after_learn       3
% 1.87/1.03  --inst_sel_renew                        solver
% 1.87/1.03  --inst_lit_activity_flag                true
% 1.87/1.03  --inst_restr_to_given                   false
% 1.87/1.03  --inst_activity_threshold               500
% 1.87/1.03  --inst_out_proof                        true
% 1.87/1.03  
% 1.87/1.03  ------ Resolution Options
% 1.87/1.03  
% 1.87/1.03  --resolution_flag                       false
% 1.87/1.03  --res_lit_sel                           adaptive
% 1.87/1.03  --res_lit_sel_side                      none
% 1.87/1.03  --res_ordering                          kbo
% 1.87/1.03  --res_to_prop_solver                    active
% 1.87/1.03  --res_prop_simpl_new                    false
% 1.87/1.03  --res_prop_simpl_given                  true
% 1.87/1.03  --res_passive_queue_type                priority_queues
% 1.87/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.87/1.03  --res_passive_queues_freq               [15;5]
% 1.87/1.03  --res_forward_subs                      full
% 1.87/1.03  --res_backward_subs                     full
% 1.87/1.03  --res_forward_subs_resolution           true
% 1.87/1.03  --res_backward_subs_resolution          true
% 1.87/1.03  --res_orphan_elimination                true
% 1.87/1.03  --res_time_limit                        2.
% 1.87/1.03  --res_out_proof                         true
% 1.87/1.03  
% 1.87/1.03  ------ Superposition Options
% 1.87/1.03  
% 1.87/1.03  --superposition_flag                    true
% 1.87/1.03  --sup_passive_queue_type                priority_queues
% 1.87/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.87/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.87/1.03  --demod_completeness_check              fast
% 1.87/1.03  --demod_use_ground                      true
% 1.87/1.03  --sup_to_prop_solver                    passive
% 1.87/1.03  --sup_prop_simpl_new                    true
% 1.87/1.03  --sup_prop_simpl_given                  true
% 1.87/1.03  --sup_fun_splitting                     false
% 1.87/1.03  --sup_smt_interval                      50000
% 1.87/1.03  
% 1.87/1.03  ------ Superposition Simplification Setup
% 1.87/1.03  
% 1.87/1.03  --sup_indices_passive                   []
% 1.87/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.87/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/1.03  --sup_full_bw                           [BwDemod]
% 1.87/1.03  --sup_immed_triv                        [TrivRules]
% 1.87/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.87/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/1.03  --sup_immed_bw_main                     []
% 1.87/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.87/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.87/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.87/1.03  
% 1.87/1.03  ------ Combination Options
% 1.87/1.03  
% 1.87/1.03  --comb_res_mult                         3
% 1.87/1.03  --comb_sup_mult                         2
% 1.87/1.03  --comb_inst_mult                        10
% 1.87/1.03  
% 1.87/1.03  ------ Debug Options
% 1.87/1.03  
% 1.87/1.03  --dbg_backtrace                         false
% 1.87/1.03  --dbg_dump_prop_clauses                 false
% 1.87/1.03  --dbg_dump_prop_clauses_file            -
% 1.87/1.03  --dbg_out_stat                          false
% 1.87/1.03  
% 1.87/1.03  
% 1.87/1.03  
% 1.87/1.03  
% 1.87/1.03  ------ Proving...
% 1.87/1.03  
% 1.87/1.03  
% 1.87/1.03  % SZS status Theorem for theBenchmark.p
% 1.87/1.03  
% 1.87/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 1.87/1.03  
% 1.87/1.03  fof(f6,axiom,(
% 1.87/1.03    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1))))))),
% 1.87/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.03  
% 1.87/1.03  fof(f15,plain,(
% 1.87/1.03    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X4) => r1_orders_2(X0,X1,X4))) & r2_lattice3(X0,X2,X1))))))),
% 1.87/1.03    inference(rectify,[],[f6])).
% 1.87/1.03  
% 1.87/1.03  fof(f26,plain,(
% 1.87/1.03    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | (~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 1.87/1.03    inference(ennf_transformation,[],[f15])).
% 1.87/1.03  
% 1.87/1.03  fof(f27,plain,(
% 1.87/1.03    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 1.87/1.03    inference(flattening,[],[f26])).
% 1.87/1.03  
% 1.87/1.03  fof(f42,plain,(
% 1.87/1.03    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X1,sK0(X0,X1,X2)) & r2_lattice3(X0,X2,sK0(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 1.87/1.03    introduced(choice_axiom,[])).
% 1.87/1.03  
% 1.87/1.03  fof(f43,plain,(
% 1.87/1.03    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (~r1_orders_2(X0,X1,sK0(X0,X1,X2)) & r2_lattice3(X0,X2,sK0(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 1.87/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f42])).
% 1.87/1.03  
% 1.87/1.03  fof(f61,plain,(
% 1.87/1.03    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X2) = X1 | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 1.87/1.03    inference(cnf_transformation,[],[f43])).
% 1.87/1.03  
% 1.87/1.03  fof(f13,conjecture,(
% 1.87/1.03    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => ((r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0))) => k1_waybel_2(X0,X2) = X1))))),
% 1.87/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.03  
% 1.87/1.03  fof(f14,negated_conjecture,(
% 1.87/1.03    ~! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => ((r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0))) => k1_waybel_2(X0,X2) = X1))))),
% 1.87/1.03    inference(negated_conjecture,[],[f13])).
% 1.87/1.03  
% 1.87/1.03  fof(f39,plain,(
% 1.87/1.03    ? [X0] : (? [X1] : (? [X2] : ((k1_waybel_2(X0,X2) != X1 & (r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))))) & (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.87/1.03    inference(ennf_transformation,[],[f14])).
% 1.87/1.03  
% 1.87/1.03  fof(f40,plain,(
% 1.87/1.03    ? [X0] : (? [X1] : (? [X2] : (k1_waybel_2(X0,X2) != X1 & r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 1.87/1.03    inference(flattening,[],[f39])).
% 1.87/1.03  
% 1.87/1.03  fof(f51,plain,(
% 1.87/1.03    ( ! [X0,X1] : (? [X2] : (k1_waybel_2(X0,X2) != X1 & r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (k1_waybel_2(X0,sK5) != X1 & r3_waybel_9(X0,sK5,X1) & v10_waybel_0(sK5,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(sK5,X0) & v7_waybel_0(sK5) & v4_orders_2(sK5) & ~v2_struct_0(sK5))) )),
% 1.87/1.03    introduced(choice_axiom,[])).
% 1.87/1.03  
% 1.87/1.03  fof(f50,plain,(
% 1.87/1.03    ( ! [X0] : (? [X1] : (? [X2] : (k1_waybel_2(X0,X2) != X1 & r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_waybel_2(X0,X2) != sK4 & r3_waybel_9(X0,X2,sK4) & v10_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 1.87/1.03    introduced(choice_axiom,[])).
% 1.87/1.03  
% 1.87/1.03  fof(f49,plain,(
% 1.87/1.03    ? [X0] : (? [X1] : (? [X2] : (k1_waybel_2(X0,X2) != X1 & r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (k1_waybel_2(sK3,X2) != X1 & r3_waybel_9(sK3,X2,X1) & v10_waybel_0(X2,sK3) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK3,X3),sK3,sK3) | ~m1_subset_1(X3,u1_struct_0(sK3))) & l1_waybel_0(X2,sK3) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_waybel_9(sK3) & v1_compts_1(sK3) & v2_lattice3(sK3) & v1_lattice3(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & v8_pre_topc(sK3) & v2_pre_topc(sK3))),
% 1.87/1.03    introduced(choice_axiom,[])).
% 1.87/1.03  
% 1.87/1.03  fof(f52,plain,(
% 1.87/1.03    ((k1_waybel_2(sK3,sK5) != sK4 & r3_waybel_9(sK3,sK5,sK4) & v10_waybel_0(sK5,sK3) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK3,X3),sK3,sK3) | ~m1_subset_1(X3,u1_struct_0(sK3))) & l1_waybel_0(sK5,sK3) & v7_waybel_0(sK5) & v4_orders_2(sK5) & ~v2_struct_0(sK5)) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_waybel_9(sK3) & v1_compts_1(sK3) & v2_lattice3(sK3) & v1_lattice3(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & v8_pre_topc(sK3) & v2_pre_topc(sK3)),
% 1.87/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f40,f51,f50,f49])).
% 1.87/1.03  
% 1.87/1.03  fof(f80,plain,(
% 1.87/1.03    v5_orders_2(sK3)),
% 1.87/1.03    inference(cnf_transformation,[],[f52])).
% 1.87/1.03  
% 1.87/1.03  fof(f84,plain,(
% 1.87/1.03    l1_waybel_9(sK3)),
% 1.87/1.03    inference(cnf_transformation,[],[f52])).
% 1.87/1.03  
% 1.87/1.03  fof(f10,axiom,(
% 1.87/1.03    ! [X0] : (l1_waybel_9(X0) => (l1_orders_2(X0) & l1_pre_topc(X0)))),
% 1.87/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.03  
% 1.87/1.03  fof(f34,plain,(
% 1.87/1.03    ! [X0] : ((l1_orders_2(X0) & l1_pre_topc(X0)) | ~l1_waybel_9(X0))),
% 1.87/1.03    inference(ennf_transformation,[],[f10])).
% 1.87/1.03  
% 1.87/1.03  fof(f71,plain,(
% 1.87/1.03    ( ! [X0] : (l1_orders_2(X0) | ~l1_waybel_9(X0)) )),
% 1.87/1.03    inference(cnf_transformation,[],[f34])).
% 1.87/1.03  
% 1.87/1.03  fof(f62,plain,(
% 1.87/1.03    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X2) = X1 | r2_lattice3(X0,X2,sK0(X0,X1,X2)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 1.87/1.03    inference(cnf_transformation,[],[f43])).
% 1.87/1.03  
% 1.87/1.03  fof(f4,axiom,(
% 1.87/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 1.87/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.03  
% 1.87/1.03  fof(f22,plain,(
% 1.87/1.03    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.87/1.03    inference(ennf_transformation,[],[f4])).
% 1.87/1.03  
% 1.87/1.03  fof(f23,plain,(
% 1.87/1.03    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.87/1.03    inference(flattening,[],[f22])).
% 1.87/1.03  
% 1.87/1.03  fof(f41,plain,(
% 1.87/1.03    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.87/1.03    inference(nnf_transformation,[],[f23])).
% 1.87/1.03  
% 1.87/1.03  fof(f56,plain,(
% 1.87/1.03    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.87/1.03    inference(cnf_transformation,[],[f41])).
% 1.87/1.03  
% 1.87/1.03  fof(f78,plain,(
% 1.87/1.03    v3_orders_2(sK3)),
% 1.87/1.03    inference(cnf_transformation,[],[f52])).
% 1.87/1.03  
% 1.87/1.03  fof(f81,plain,(
% 1.87/1.03    v1_lattice3(sK3)),
% 1.87/1.03    inference(cnf_transformation,[],[f52])).
% 1.87/1.03  
% 1.87/1.03  fof(f5,axiom,(
% 1.87/1.03    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 1.87/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.03  
% 1.87/1.03  fof(f24,plain,(
% 1.87/1.03    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 1.87/1.03    inference(ennf_transformation,[],[f5])).
% 1.87/1.03  
% 1.87/1.03  fof(f25,plain,(
% 1.87/1.03    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 1.87/1.03    inference(flattening,[],[f24])).
% 1.87/1.03  
% 1.87/1.03  fof(f58,plain,(
% 1.87/1.03    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 1.87/1.03    inference(cnf_transformation,[],[f25])).
% 1.87/1.03  
% 1.87/1.03  fof(f92,plain,(
% 1.87/1.03    r3_waybel_9(sK3,sK5,sK4)),
% 1.87/1.03    inference(cnf_transformation,[],[f52])).
% 1.87/1.03  
% 1.87/1.03  fof(f88,plain,(
% 1.87/1.03    v7_waybel_0(sK5)),
% 1.87/1.03    inference(cnf_transformation,[],[f52])).
% 1.87/1.03  
% 1.87/1.03  fof(f12,axiom,(
% 1.87/1.03    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) => r3_orders_2(X0,X3,X4))))))))),
% 1.87/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.03  
% 1.87/1.03  fof(f16,plain,(
% 1.87/1.03    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) => r3_orders_2(X0,X3,X5))))))))),
% 1.87/1.03    inference(rectify,[],[f12])).
% 1.87/1.03  
% 1.87/1.03  fof(f37,plain,(
% 1.87/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X5] : ((r3_orders_2(X0,X3,X5) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)) | ~m1_subset_1(X5,u1_struct_0(X0))) | (~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.87/1.03    inference(ennf_transformation,[],[f16])).
% 1.87/1.03  
% 1.87/1.03  fof(f38,plain,(
% 1.87/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X5] : (r3_orders_2(X0,X3,X5) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.87/1.03    inference(flattening,[],[f37])).
% 1.87/1.03  
% 1.87/1.03  fof(f46,plain,(
% 1.87/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | ? [X5] : (~v5_pre_topc(k4_waybel_1(X0,X5),X0,X0) & m1_subset_1(X5,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.87/1.03    inference(rectify,[],[f38])).
% 1.87/1.03  
% 1.87/1.03  fof(f47,plain,(
% 1.87/1.03    ! [X0] : (? [X5] : (~v5_pre_topc(k4_waybel_1(X0,X5),X0,X0) & m1_subset_1(X5,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0) & m1_subset_1(sK2(X0),u1_struct_0(X0))))),
% 1.87/1.03    introduced(choice_axiom,[])).
% 1.87/1.03  
% 1.87/1.03  fof(f48,plain,(
% 1.87/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | (~v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0) & m1_subset_1(sK2(X0),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.87/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f46,f47])).
% 1.87/1.03  
% 1.87/1.03  fof(f75,plain,(
% 1.87/1.03    ( ! [X4,X2,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | ~v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.87/1.03    inference(cnf_transformation,[],[f48])).
% 1.87/1.03  
% 1.87/1.03  fof(f98,plain,(
% 1.87/1.03    ( ! [X4,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | ~v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.87/1.03    inference(equality_resolution,[],[f75])).
% 1.87/1.03  
% 1.87/1.03  fof(f90,plain,(
% 1.87/1.03    ( ! [X3] : (v5_pre_topc(k4_waybel_1(sK3,X3),sK3,sK3) | ~m1_subset_1(X3,u1_struct_0(sK3))) )),
% 1.87/1.03    inference(cnf_transformation,[],[f52])).
% 1.87/1.03  
% 1.87/1.03  fof(f76,plain,(
% 1.87/1.03    v2_pre_topc(sK3)),
% 1.87/1.03    inference(cnf_transformation,[],[f52])).
% 1.87/1.03  
% 1.87/1.03  fof(f77,plain,(
% 1.87/1.03    v8_pre_topc(sK3)),
% 1.87/1.03    inference(cnf_transformation,[],[f52])).
% 1.87/1.03  
% 1.87/1.03  fof(f79,plain,(
% 1.87/1.03    v4_orders_2(sK3)),
% 1.87/1.03    inference(cnf_transformation,[],[f52])).
% 1.87/1.03  
% 1.87/1.03  fof(f82,plain,(
% 1.87/1.03    v2_lattice3(sK3)),
% 1.87/1.03    inference(cnf_transformation,[],[f52])).
% 1.87/1.03  
% 1.87/1.03  fof(f83,plain,(
% 1.87/1.03    v1_compts_1(sK3)),
% 1.87/1.03    inference(cnf_transformation,[],[f52])).
% 1.87/1.03  
% 1.87/1.03  fof(f86,plain,(
% 1.87/1.03    ~v2_struct_0(sK5)),
% 1.87/1.03    inference(cnf_transformation,[],[f52])).
% 1.87/1.03  
% 1.87/1.03  fof(f87,plain,(
% 1.87/1.03    v4_orders_2(sK5)),
% 1.87/1.03    inference(cnf_transformation,[],[f52])).
% 1.87/1.03  
% 1.87/1.03  fof(f89,plain,(
% 1.87/1.03    l1_waybel_0(sK5,sK3)),
% 1.87/1.03    inference(cnf_transformation,[],[f52])).
% 1.87/1.03  
% 1.87/1.03  fof(f85,plain,(
% 1.87/1.03    m1_subset_1(sK4,u1_struct_0(sK3))),
% 1.87/1.03    inference(cnf_transformation,[],[f52])).
% 1.87/1.03  
% 1.87/1.03  fof(f74,plain,(
% 1.87/1.03    ( ! [X4,X2,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | m1_subset_1(sK2(X0),u1_struct_0(X0)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.87/1.03    inference(cnf_transformation,[],[f48])).
% 1.87/1.03  
% 1.87/1.03  fof(f99,plain,(
% 1.87/1.03    ( ! [X4,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | m1_subset_1(sK2(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.87/1.03    inference(equality_resolution,[],[f74])).
% 1.87/1.03  
% 1.87/1.03  fof(f7,axiom,(
% 1.87/1.03    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 1.87/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.03  
% 1.87/1.03  fof(f17,plain,(
% 1.87/1.03    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 1.87/1.03    inference(pure_predicate_removal,[],[f7])).
% 1.87/1.03  
% 1.87/1.03  fof(f18,plain,(
% 1.87/1.03    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))))),
% 1.87/1.03    inference(pure_predicate_removal,[],[f17])).
% 1.87/1.03  
% 1.87/1.03  fof(f28,plain,(
% 1.87/1.03    ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 1.87/1.03    inference(ennf_transformation,[],[f18])).
% 1.87/1.03  
% 1.87/1.03  fof(f29,plain,(
% 1.87/1.03    ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 1.87/1.03    inference(flattening,[],[f28])).
% 1.87/1.03  
% 1.87/1.03  fof(f67,plain,(
% 1.87/1.03    ( ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 1.87/1.03    inference(cnf_transformation,[],[f29])).
% 1.87/1.03  
% 1.87/1.03  fof(f70,plain,(
% 1.87/1.03    ( ! [X0] : (l1_pre_topc(X0) | ~l1_waybel_9(X0)) )),
% 1.87/1.03    inference(cnf_transformation,[],[f34])).
% 1.87/1.03  
% 1.87/1.03  fof(f3,axiom,(
% 1.87/1.03    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.87/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.03  
% 1.87/1.03  fof(f21,plain,(
% 1.87/1.03    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.87/1.03    inference(ennf_transformation,[],[f3])).
% 1.87/1.03  
% 1.87/1.03  fof(f55,plain,(
% 1.87/1.03    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.87/1.03    inference(cnf_transformation,[],[f21])).
% 1.87/1.03  
% 1.87/1.03  fof(f2,axiom,(
% 1.87/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.87/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.03  
% 1.87/1.03  fof(f20,plain,(
% 1.87/1.03    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.87/1.03    inference(ennf_transformation,[],[f2])).
% 1.87/1.03  
% 1.87/1.03  fof(f54,plain,(
% 1.87/1.03    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.87/1.03    inference(cnf_transformation,[],[f20])).
% 1.87/1.03  
% 1.87/1.03  fof(f1,axiom,(
% 1.87/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.87/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.03  
% 1.87/1.03  fof(f19,plain,(
% 1.87/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.87/1.03    inference(ennf_transformation,[],[f1])).
% 1.87/1.03  
% 1.87/1.03  fof(f53,plain,(
% 1.87/1.03    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.87/1.03    inference(cnf_transformation,[],[f19])).
% 1.87/1.03  
% 1.87/1.03  fof(f9,axiom,(
% 1.87/1.03    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (v1_relat_1(X1) => k1_yellow_0(X0,k2_relat_1(X1)) = k4_yellow_2(X0,X1)))),
% 1.87/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.03  
% 1.87/1.03  fof(f32,plain,(
% 1.87/1.03    ! [X0] : (! [X1] : (k1_yellow_0(X0,k2_relat_1(X1)) = k4_yellow_2(X0,X1) | ~v1_relat_1(X1)) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 1.87/1.03    inference(ennf_transformation,[],[f9])).
% 1.87/1.03  
% 1.87/1.03  fof(f33,plain,(
% 1.87/1.03    ! [X0] : (! [X1] : (k1_yellow_0(X0,k2_relat_1(X1)) = k4_yellow_2(X0,X1) | ~v1_relat_1(X1)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 1.87/1.03    inference(flattening,[],[f32])).
% 1.87/1.03  
% 1.87/1.03  fof(f69,plain,(
% 1.87/1.03    ( ! [X0,X1] : (k1_yellow_0(X0,k2_relat_1(X1)) = k4_yellow_2(X0,X1) | ~v1_relat_1(X1) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 1.87/1.03    inference(cnf_transformation,[],[f33])).
% 1.87/1.03  
% 1.87/1.03  fof(f8,axiom,(
% 1.87/1.03    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (l1_waybel_0(X1,X0) => k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1))))),
% 1.87/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.03  
% 1.87/1.03  fof(f30,plain,(
% 1.87/1.03    ! [X0] : (! [X1] : (k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0)) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 1.87/1.03    inference(ennf_transformation,[],[f8])).
% 1.87/1.03  
% 1.87/1.03  fof(f31,plain,(
% 1.87/1.03    ! [X0] : (! [X1] : (k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 1.87/1.03    inference(flattening,[],[f30])).
% 1.87/1.03  
% 1.87/1.03  fof(f68,plain,(
% 1.87/1.03    ( ! [X0,X1] : (k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 1.87/1.03    inference(cnf_transformation,[],[f31])).
% 1.87/1.03  
% 1.87/1.03  fof(f63,plain,(
% 1.87/1.03    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X2) = X1 | ~r1_orders_2(X0,X1,sK0(X0,X1,X2)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 1.87/1.03    inference(cnf_transformation,[],[f43])).
% 1.87/1.03  
% 1.87/1.03  fof(f11,axiom,(
% 1.87/1.03    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & v10_waybel_0(X1,X0) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3))))))),
% 1.87/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.03  
% 1.87/1.03  fof(f35,plain,(
% 1.87/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | (~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.87/1.03    inference(ennf_transformation,[],[f11])).
% 1.87/1.03  
% 1.87/1.03  fof(f36,plain,(
% 1.87/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.87/1.03    inference(flattening,[],[f35])).
% 1.87/1.03  
% 1.87/1.03  fof(f44,plain,(
% 1.87/1.03    ! [X0] : (? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0) & m1_subset_1(sK1(X0),u1_struct_0(X0))))),
% 1.87/1.03    introduced(choice_axiom,[])).
% 1.87/1.03  
% 1.87/1.03  fof(f45,plain,(
% 1.87/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | (~v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0) & m1_subset_1(sK1(X0),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.87/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f44])).
% 1.87/1.03  
% 1.87/1.03  fof(f73,plain,(
% 1.87/1.03    ( ! [X2,X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.87/1.03    inference(cnf_transformation,[],[f45])).
% 1.87/1.03  
% 1.87/1.03  fof(f96,plain,(
% 1.87/1.03    ( ! [X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v10_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.87/1.03    inference(equality_resolution,[],[f73])).
% 1.87/1.03  
% 1.87/1.03  fof(f91,plain,(
% 1.87/1.03    v10_waybel_0(sK5,sK3)),
% 1.87/1.03    inference(cnf_transformation,[],[f52])).
% 1.87/1.03  
% 1.87/1.03  fof(f72,plain,(
% 1.87/1.03    ( ! [X2,X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | m1_subset_1(sK1(X0),u1_struct_0(X0)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.87/1.03    inference(cnf_transformation,[],[f45])).
% 1.87/1.03  
% 1.87/1.03  fof(f97,plain,(
% 1.87/1.03    ( ! [X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v10_waybel_0(X1,X0) | m1_subset_1(sK1(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.87/1.03    inference(equality_resolution,[],[f72])).
% 1.87/1.03  
% 1.87/1.03  fof(f93,plain,(
% 1.87/1.03    k1_waybel_2(sK3,sK5) != sK4),
% 1.87/1.03    inference(cnf_transformation,[],[f52])).
% 1.87/1.03  
% 1.87/1.03  cnf(c_11,plain,
% 1.87/1.03      ( ~ r2_lattice3(X0,X1,X2)
% 1.87/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.87/1.03      | m1_subset_1(sK0(X0,X2,X1),u1_struct_0(X0))
% 1.87/1.03      | ~ v5_orders_2(X0)
% 1.87/1.03      | ~ l1_orders_2(X0)
% 1.87/1.03      | k1_yellow_0(X0,X1) = X2 ),
% 1.87/1.03      inference(cnf_transformation,[],[f61]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_36,negated_conjecture,
% 1.87/1.03      ( v5_orders_2(sK3) ),
% 1.87/1.03      inference(cnf_transformation,[],[f80]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_1162,plain,
% 1.87/1.03      ( ~ r2_lattice3(X0,X1,X2)
% 1.87/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.87/1.03      | m1_subset_1(sK0(X0,X2,X1),u1_struct_0(X0))
% 1.87/1.03      | ~ l1_orders_2(X0)
% 1.87/1.03      | k1_yellow_0(X0,X1) = X2
% 1.87/1.03      | sK3 != X0 ),
% 1.87/1.03      inference(resolution_lifted,[status(thm)],[c_11,c_36]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_1163,plain,
% 1.87/1.03      ( ~ r2_lattice3(sK3,X0,X1)
% 1.87/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/1.03      | m1_subset_1(sK0(sK3,X1,X0),u1_struct_0(sK3))
% 1.87/1.03      | ~ l1_orders_2(sK3)
% 1.87/1.03      | k1_yellow_0(sK3,X0) = X1 ),
% 1.87/1.03      inference(unflattening,[status(thm)],[c_1162]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_32,negated_conjecture,
% 1.87/1.03      ( l1_waybel_9(sK3) ),
% 1.87/1.03      inference(cnf_transformation,[],[f84]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_17,plain,
% 1.87/1.03      ( ~ l1_waybel_9(X0) | l1_orders_2(X0) ),
% 1.87/1.03      inference(cnf_transformation,[],[f71]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_76,plain,
% 1.87/1.03      ( ~ l1_waybel_9(sK3) | l1_orders_2(sK3) ),
% 1.87/1.03      inference(instantiation,[status(thm)],[c_17]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_1167,plain,
% 1.87/1.03      ( m1_subset_1(sK0(sK3,X1,X0),u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/1.03      | ~ r2_lattice3(sK3,X0,X1)
% 1.87/1.03      | k1_yellow_0(sK3,X0) = X1 ),
% 1.87/1.03      inference(global_propositional_subsumption,
% 1.87/1.03                [status(thm)],
% 1.87/1.03                [c_1163,c_32,c_76]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_1168,plain,
% 1.87/1.03      ( ~ r2_lattice3(sK3,X0,X1)
% 1.87/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/1.03      | m1_subset_1(sK0(sK3,X1,X0),u1_struct_0(sK3))
% 1.87/1.03      | k1_yellow_0(sK3,X0) = X1 ),
% 1.87/1.03      inference(renaming,[status(thm)],[c_1167]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_2261,plain,
% 1.87/1.03      ( ~ r2_lattice3(sK3,X0_70,X0_68)
% 1.87/1.03      | ~ m1_subset_1(X0_68,u1_struct_0(sK3))
% 1.87/1.03      | m1_subset_1(sK0(sK3,X0_68,X0_70),u1_struct_0(sK3))
% 1.87/1.03      | k1_yellow_0(sK3,X0_70) = X0_68 ),
% 1.87/1.03      inference(subtyping,[status(esa)],[c_1168]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_2715,plain,
% 1.87/1.03      ( k1_yellow_0(sK3,X0_70) = X0_68
% 1.87/1.03      | r2_lattice3(sK3,X0_70,X0_68) != iProver_top
% 1.87/1.03      | m1_subset_1(X0_68,u1_struct_0(sK3)) != iProver_top
% 1.87/1.03      | m1_subset_1(sK0(sK3,X0_68,X0_70),u1_struct_0(sK3)) = iProver_top ),
% 1.87/1.03      inference(predicate_to_equality,[status(thm)],[c_2261]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_10,plain,
% 1.87/1.03      ( ~ r2_lattice3(X0,X1,X2)
% 1.87/1.03      | r2_lattice3(X0,X1,sK0(X0,X2,X1))
% 1.87/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.87/1.03      | ~ v5_orders_2(X0)
% 1.87/1.03      | ~ l1_orders_2(X0)
% 1.87/1.03      | k1_yellow_0(X0,X1) = X2 ),
% 1.87/1.03      inference(cnf_transformation,[],[f62]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_1186,plain,
% 1.87/1.03      ( ~ r2_lattice3(X0,X1,X2)
% 1.87/1.03      | r2_lattice3(X0,X1,sK0(X0,X2,X1))
% 1.87/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.87/1.03      | ~ l1_orders_2(X0)
% 1.87/1.03      | k1_yellow_0(X0,X1) = X2
% 1.87/1.03      | sK3 != X0 ),
% 1.87/1.03      inference(resolution_lifted,[status(thm)],[c_10,c_36]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_1187,plain,
% 1.87/1.03      ( ~ r2_lattice3(sK3,X0,X1)
% 1.87/1.03      | r2_lattice3(sK3,X0,sK0(sK3,X1,X0))
% 1.87/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/1.03      | ~ l1_orders_2(sK3)
% 1.87/1.03      | k1_yellow_0(sK3,X0) = X1 ),
% 1.87/1.03      inference(unflattening,[status(thm)],[c_1186]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_1191,plain,
% 1.87/1.03      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/1.03      | r2_lattice3(sK3,X0,sK0(sK3,X1,X0))
% 1.87/1.03      | ~ r2_lattice3(sK3,X0,X1)
% 1.87/1.03      | k1_yellow_0(sK3,X0) = X1 ),
% 1.87/1.03      inference(global_propositional_subsumption,
% 1.87/1.03                [status(thm)],
% 1.87/1.03                [c_1187,c_32,c_76]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_1192,plain,
% 1.87/1.03      ( ~ r2_lattice3(sK3,X0,X1)
% 1.87/1.03      | r2_lattice3(sK3,X0,sK0(sK3,X1,X0))
% 1.87/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/1.03      | k1_yellow_0(sK3,X0) = X1 ),
% 1.87/1.03      inference(renaming,[status(thm)],[c_1191]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_2260,plain,
% 1.87/1.03      ( ~ r2_lattice3(sK3,X0_70,X0_68)
% 1.87/1.03      | r2_lattice3(sK3,X0_70,sK0(sK3,X0_68,X0_70))
% 1.87/1.03      | ~ m1_subset_1(X0_68,u1_struct_0(sK3))
% 1.87/1.03      | k1_yellow_0(sK3,X0_70) = X0_68 ),
% 1.87/1.03      inference(subtyping,[status(esa)],[c_1192]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_2716,plain,
% 1.87/1.03      ( k1_yellow_0(sK3,X0_70) = X0_68
% 1.87/1.03      | r2_lattice3(sK3,X0_70,X0_68) != iProver_top
% 1.87/1.03      | r2_lattice3(sK3,X0_70,sK0(sK3,X0_68,X0_70)) = iProver_top
% 1.87/1.03      | m1_subset_1(X0_68,u1_struct_0(sK3)) != iProver_top ),
% 1.87/1.03      inference(predicate_to_equality,[status(thm)],[c_2260]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_4,plain,
% 1.87/1.03      ( r1_orders_2(X0,X1,X2)
% 1.87/1.03      | ~ r3_orders_2(X0,X1,X2)
% 1.87/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.87/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.87/1.03      | v2_struct_0(X0)
% 1.87/1.03      | ~ v3_orders_2(X0)
% 1.87/1.03      | ~ l1_orders_2(X0) ),
% 1.87/1.03      inference(cnf_transformation,[],[f56]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_38,negated_conjecture,
% 1.87/1.03      ( v3_orders_2(sK3) ),
% 1.87/1.03      inference(cnf_transformation,[],[f78]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_723,plain,
% 1.87/1.03      ( r1_orders_2(X0,X1,X2)
% 1.87/1.03      | ~ r3_orders_2(X0,X1,X2)
% 1.87/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.87/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.87/1.03      | v2_struct_0(X0)
% 1.87/1.03      | ~ l1_orders_2(X0)
% 1.87/1.03      | sK3 != X0 ),
% 1.87/1.03      inference(resolution_lifted,[status(thm)],[c_4,c_38]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_724,plain,
% 1.87/1.03      ( r1_orders_2(sK3,X0,X1)
% 1.87/1.03      | ~ r3_orders_2(sK3,X0,X1)
% 1.87/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/1.03      | v2_struct_0(sK3)
% 1.87/1.03      | ~ l1_orders_2(sK3) ),
% 1.87/1.03      inference(unflattening,[status(thm)],[c_723]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_35,negated_conjecture,
% 1.87/1.03      ( v1_lattice3(sK3) ),
% 1.87/1.03      inference(cnf_transformation,[],[f81]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_5,plain,
% 1.87/1.03      ( ~ v1_lattice3(X0) | ~ v2_struct_0(X0) | ~ l1_orders_2(X0) ),
% 1.87/1.03      inference(cnf_transformation,[],[f58]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_112,plain,
% 1.87/1.03      ( ~ v1_lattice3(sK3) | ~ v2_struct_0(sK3) | ~ l1_orders_2(sK3) ),
% 1.87/1.03      inference(instantiation,[status(thm)],[c_5]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_728,plain,
% 1.87/1.03      ( r1_orders_2(sK3,X0,X1)
% 1.87/1.03      | ~ r3_orders_2(sK3,X0,X1)
% 1.87/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 1.87/1.03      inference(global_propositional_subsumption,
% 1.87/1.03                [status(thm)],
% 1.87/1.03                [c_724,c_35,c_32,c_76,c_112]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_729,plain,
% 1.87/1.03      ( r1_orders_2(sK3,X0,X1)
% 1.87/1.03      | ~ r3_orders_2(sK3,X0,X1)
% 1.87/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
% 1.87/1.03      inference(renaming,[status(thm)],[c_728]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_24,negated_conjecture,
% 1.87/1.03      ( r3_waybel_9(sK3,sK5,sK4) ),
% 1.87/1.03      inference(cnf_transformation,[],[f92]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_28,negated_conjecture,
% 1.87/1.03      ( v7_waybel_0(sK5) ),
% 1.87/1.03      inference(cnf_transformation,[],[f88]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_21,plain,
% 1.87/1.03      ( ~ v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0)
% 1.87/1.03      | ~ r3_waybel_9(X0,X1,X2)
% 1.87/1.03      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 1.87/1.03      | r3_orders_2(X0,X2,X3)
% 1.87/1.03      | ~ l1_waybel_0(X1,X0)
% 1.87/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.87/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.87/1.03      | ~ v2_pre_topc(X0)
% 1.87/1.03      | ~ v8_pre_topc(X0)
% 1.87/1.03      | ~ v2_lattice3(X0)
% 1.87/1.03      | ~ v1_compts_1(X0)
% 1.87/1.03      | ~ v4_orders_2(X1)
% 1.87/1.03      | ~ v4_orders_2(X0)
% 1.87/1.03      | ~ v7_waybel_0(X1)
% 1.87/1.03      | ~ l1_waybel_9(X0)
% 1.87/1.03      | ~ v5_orders_2(X0)
% 1.87/1.03      | ~ v1_lattice3(X0)
% 1.87/1.03      | v2_struct_0(X1)
% 1.87/1.03      | ~ v3_orders_2(X0) ),
% 1.87/1.03      inference(cnf_transformation,[],[f98]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_26,negated_conjecture,
% 1.87/1.03      ( v5_pre_topc(k4_waybel_1(sK3,X0),sK3,sK3)
% 1.87/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 1.87/1.03      inference(cnf_transformation,[],[f90]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_557,plain,
% 1.87/1.03      ( ~ r3_waybel_9(X0,X1,X2)
% 1.87/1.03      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 1.87/1.03      | r3_orders_2(X0,X2,X3)
% 1.87/1.03      | ~ l1_waybel_0(X1,X0)
% 1.87/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.87/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.87/1.03      | ~ m1_subset_1(X4,u1_struct_0(sK3))
% 1.87/1.03      | ~ v2_pre_topc(X0)
% 1.87/1.03      | ~ v8_pre_topc(X0)
% 1.87/1.03      | ~ v2_lattice3(X0)
% 1.87/1.03      | ~ v1_compts_1(X0)
% 1.87/1.03      | ~ v4_orders_2(X1)
% 1.87/1.03      | ~ v4_orders_2(X0)
% 1.87/1.03      | ~ v7_waybel_0(X1)
% 1.87/1.03      | ~ l1_waybel_9(X0)
% 1.87/1.03      | ~ v5_orders_2(X0)
% 1.87/1.03      | ~ v1_lattice3(X0)
% 1.87/1.03      | v2_struct_0(X1)
% 1.87/1.03      | ~ v3_orders_2(X0)
% 1.87/1.03      | k4_waybel_1(X0,sK2(X0)) != k4_waybel_1(sK3,X4)
% 1.87/1.03      | sK3 != X0 ),
% 1.87/1.03      inference(resolution_lifted,[status(thm)],[c_21,c_26]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_558,plain,
% 1.87/1.03      ( ~ r3_waybel_9(sK3,X0,X1)
% 1.87/1.03      | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
% 1.87/1.03      | r3_orders_2(sK3,X1,X2)
% 1.87/1.03      | ~ l1_waybel_0(X0,sK3)
% 1.87/1.03      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.87/1.03      | ~ v2_pre_topc(sK3)
% 1.87/1.03      | ~ v8_pre_topc(sK3)
% 1.87/1.03      | ~ v2_lattice3(sK3)
% 1.87/1.03      | ~ v1_compts_1(sK3)
% 1.87/1.03      | ~ v4_orders_2(X0)
% 1.87/1.03      | ~ v4_orders_2(sK3)
% 1.87/1.03      | ~ v7_waybel_0(X0)
% 1.87/1.03      | ~ l1_waybel_9(sK3)
% 1.87/1.03      | ~ v5_orders_2(sK3)
% 1.87/1.03      | ~ v1_lattice3(sK3)
% 1.87/1.03      | v2_struct_0(X0)
% 1.87/1.03      | ~ v3_orders_2(sK3)
% 1.87/1.03      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X3) ),
% 1.87/1.03      inference(unflattening,[status(thm)],[c_557]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_40,negated_conjecture,
% 1.87/1.03      ( v2_pre_topc(sK3) ),
% 1.87/1.03      inference(cnf_transformation,[],[f76]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_39,negated_conjecture,
% 1.87/1.03      ( v8_pre_topc(sK3) ),
% 1.87/1.03      inference(cnf_transformation,[],[f77]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_37,negated_conjecture,
% 1.87/1.03      ( v4_orders_2(sK3) ),
% 1.87/1.03      inference(cnf_transformation,[],[f79]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_34,negated_conjecture,
% 1.87/1.03      ( v2_lattice3(sK3) ),
% 1.87/1.03      inference(cnf_transformation,[],[f82]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_33,negated_conjecture,
% 1.87/1.03      ( v1_compts_1(sK3) ),
% 1.87/1.03      inference(cnf_transformation,[],[f83]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_562,plain,
% 1.87/1.03      ( v2_struct_0(X0)
% 1.87/1.03      | ~ v4_orders_2(X0)
% 1.87/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 1.87/1.03      | ~ l1_waybel_0(X0,sK3)
% 1.87/1.03      | r3_orders_2(sK3,X1,X2)
% 1.87/1.03      | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
% 1.87/1.03      | ~ r3_waybel_9(sK3,X0,X1)
% 1.87/1.03      | ~ v7_waybel_0(X0)
% 1.87/1.03      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X3) ),
% 1.87/1.03      inference(global_propositional_subsumption,
% 1.87/1.03                [status(thm)],
% 1.87/1.03                [c_558,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_563,plain,
% 1.87/1.03      ( ~ r3_waybel_9(sK3,X0,X1)
% 1.87/1.03      | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
% 1.87/1.03      | r3_orders_2(sK3,X1,X2)
% 1.87/1.03      | ~ l1_waybel_0(X0,sK3)
% 1.87/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/1.03      | ~ v4_orders_2(X0)
% 1.87/1.03      | ~ v7_waybel_0(X0)
% 1.87/1.03      | v2_struct_0(X0)
% 1.87/1.03      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X3) ),
% 1.87/1.03      inference(renaming,[status(thm)],[c_562]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_811,plain,
% 1.87/1.03      ( ~ r3_waybel_9(sK3,X0,X1)
% 1.87/1.03      | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
% 1.87/1.03      | r3_orders_2(sK3,X1,X2)
% 1.87/1.03      | ~ l1_waybel_0(X0,sK3)
% 1.87/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/1.03      | ~ v4_orders_2(X0)
% 1.87/1.03      | v2_struct_0(X0)
% 1.87/1.03      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X3)
% 1.87/1.03      | sK5 != X0 ),
% 1.87/1.03      inference(resolution_lifted,[status(thm)],[c_28,c_563]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_812,plain,
% 1.87/1.03      ( ~ r3_waybel_9(sK3,sK5,X0)
% 1.87/1.03      | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
% 1.87/1.03      | r3_orders_2(sK3,X0,X1)
% 1.87/1.03      | ~ l1_waybel_0(sK5,sK3)
% 1.87/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/1.03      | ~ v4_orders_2(sK5)
% 1.87/1.03      | v2_struct_0(sK5)
% 1.87/1.03      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X2) ),
% 1.87/1.03      inference(unflattening,[status(thm)],[c_811]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_30,negated_conjecture,
% 1.87/1.03      ( ~ v2_struct_0(sK5) ),
% 1.87/1.03      inference(cnf_transformation,[],[f86]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_29,negated_conjecture,
% 1.87/1.03      ( v4_orders_2(sK5) ),
% 1.87/1.03      inference(cnf_transformation,[],[f87]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_27,negated_conjecture,
% 1.87/1.03      ( l1_waybel_0(sK5,sK3) ),
% 1.87/1.03      inference(cnf_transformation,[],[f89]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_816,plain,
% 1.87/1.03      ( r3_orders_2(sK3,X0,X1)
% 1.87/1.03      | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
% 1.87/1.03      | ~ r3_waybel_9(sK3,sK5,X0)
% 1.87/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/1.03      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X2) ),
% 1.87/1.03      inference(global_propositional_subsumption,
% 1.87/1.03                [status(thm)],
% 1.87/1.03                [c_812,c_30,c_29,c_27]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_817,plain,
% 1.87/1.03      ( ~ r3_waybel_9(sK3,sK5,X0)
% 1.87/1.03      | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
% 1.87/1.03      | r3_orders_2(sK3,X0,X1)
% 1.87/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/1.03      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X2) ),
% 1.87/1.03      inference(renaming,[status(thm)],[c_816]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_947,plain,
% 1.87/1.03      ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.87/1.03      | r3_orders_2(sK3,X1,X0)
% 1.87/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/1.03      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X2)
% 1.87/1.03      | sK4 != X1
% 1.87/1.03      | sK5 != sK5
% 1.87/1.03      | sK3 != sK3 ),
% 1.87/1.03      inference(resolution_lifted,[status(thm)],[c_24,c_817]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_948,plain,
% 1.87/1.03      ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.87/1.03      | r3_orders_2(sK3,sK4,X0)
% 1.87/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 1.87/1.03      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1) ),
% 1.87/1.03      inference(unflattening,[status(thm)],[c_947]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_31,negated_conjecture,
% 1.87/1.03      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 1.87/1.03      inference(cnf_transformation,[],[f85]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_952,plain,
% 1.87/1.03      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/1.03      | r3_orders_2(sK3,sK4,X0)
% 1.87/1.03      | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.87/1.03      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1) ),
% 1.87/1.03      inference(global_propositional_subsumption,
% 1.87/1.03                [status(thm)],
% 1.87/1.03                [c_948,c_31]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_953,plain,
% 1.87/1.03      ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.87/1.03      | r3_orders_2(sK3,sK4,X0)
% 1.87/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/1.03      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1) ),
% 1.87/1.03      inference(renaming,[status(thm)],[c_952]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_1076,plain,
% 1.87/1.03      ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.87/1.03      | r1_orders_2(sK3,X1,X2)
% 1.87/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.87/1.03      | X0 != X2
% 1.87/1.03      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X3)
% 1.87/1.03      | sK4 != X1
% 1.87/1.03      | sK3 != sK3 ),
% 1.87/1.03      inference(resolution_lifted,[status(thm)],[c_729,c_953]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_1077,plain,
% 1.87/1.03      ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.87/1.03      | r1_orders_2(sK3,sK4,X0)
% 1.87/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 1.87/1.03      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1) ),
% 1.87/1.03      inference(unflattening,[status(thm)],[c_1076]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_1081,plain,
% 1.87/1.03      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/1.03      | r1_orders_2(sK3,sK4,X0)
% 1.87/1.03      | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.87/1.03      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1) ),
% 1.87/1.03      inference(global_propositional_subsumption,
% 1.87/1.03                [status(thm)],
% 1.87/1.03                [c_1077,c_31]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_1082,plain,
% 1.87/1.03      ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.87/1.03      | r1_orders_2(sK3,sK4,X0)
% 1.87/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/1.03      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1) ),
% 1.87/1.03      inference(renaming,[status(thm)],[c_1081]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_2264,plain,
% 1.87/1.03      ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_68)
% 1.87/1.03      | r1_orders_2(sK3,sK4,X0_68)
% 1.87/1.03      | ~ m1_subset_1(X1_68,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X0_68,u1_struct_0(sK3))
% 1.87/1.03      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1_68) ),
% 1.87/1.03      inference(subtyping,[status(esa)],[c_1082]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_2276,plain,
% 1.87/1.03      ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_68)
% 1.87/1.03      | r1_orders_2(sK3,sK4,X0_68)
% 1.87/1.03      | ~ m1_subset_1(X0_68,u1_struct_0(sK3))
% 1.87/1.03      | ~ sP1_iProver_split ),
% 1.87/1.03      inference(splitting,
% 1.87/1.03                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 1.87/1.03                [c_2264]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_2711,plain,
% 1.87/1.03      ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_68) != iProver_top
% 1.87/1.03      | r1_orders_2(sK3,sK4,X0_68) = iProver_top
% 1.87/1.03      | m1_subset_1(X0_68,u1_struct_0(sK3)) != iProver_top
% 1.87/1.03      | sP1_iProver_split != iProver_top ),
% 1.87/1.03      inference(predicate_to_equality,[status(thm)],[c_2276]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_22,plain,
% 1.87/1.03      ( ~ r3_waybel_9(X0,X1,X2)
% 1.87/1.03      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 1.87/1.03      | r3_orders_2(X0,X2,X3)
% 1.87/1.03      | ~ l1_waybel_0(X1,X0)
% 1.87/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.87/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.87/1.03      | m1_subset_1(sK2(X0),u1_struct_0(X0))
% 1.87/1.03      | ~ v2_pre_topc(X0)
% 1.87/1.03      | ~ v8_pre_topc(X0)
% 1.87/1.03      | ~ v2_lattice3(X0)
% 1.87/1.03      | ~ v1_compts_1(X0)
% 1.87/1.03      | ~ v4_orders_2(X1)
% 1.87/1.03      | ~ v4_orders_2(X0)
% 1.87/1.03      | ~ v7_waybel_0(X1)
% 1.87/1.03      | ~ l1_waybel_9(X0)
% 1.87/1.03      | ~ v5_orders_2(X0)
% 1.87/1.03      | ~ v1_lattice3(X0)
% 1.87/1.03      | v2_struct_0(X1)
% 1.87/1.03      | ~ v3_orders_2(X0) ),
% 1.87/1.03      inference(cnf_transformation,[],[f99]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_633,plain,
% 1.87/1.03      ( ~ r3_waybel_9(X0,X1,X2)
% 1.87/1.03      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 1.87/1.03      | r3_orders_2(X0,X2,X3)
% 1.87/1.03      | ~ l1_waybel_0(X1,X0)
% 1.87/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.87/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.87/1.03      | m1_subset_1(sK2(X0),u1_struct_0(X0))
% 1.87/1.03      | ~ v2_pre_topc(X0)
% 1.87/1.03      | ~ v8_pre_topc(X0)
% 1.87/1.03      | ~ v2_lattice3(X0)
% 1.87/1.03      | ~ v4_orders_2(X1)
% 1.87/1.03      | ~ v4_orders_2(X0)
% 1.87/1.03      | ~ v7_waybel_0(X1)
% 1.87/1.03      | ~ l1_waybel_9(X0)
% 1.87/1.03      | ~ v5_orders_2(X0)
% 1.87/1.03      | ~ v1_lattice3(X0)
% 1.87/1.03      | v2_struct_0(X1)
% 1.87/1.03      | ~ v3_orders_2(X0)
% 1.87/1.03      | sK3 != X0 ),
% 1.87/1.03      inference(resolution_lifted,[status(thm)],[c_22,c_33]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_634,plain,
% 1.87/1.03      ( ~ r3_waybel_9(sK3,X0,X1)
% 1.87/1.03      | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
% 1.87/1.03      | r3_orders_2(sK3,X1,X2)
% 1.87/1.03      | ~ l1_waybel_0(X0,sK3)
% 1.87/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.87/1.03      | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
% 1.87/1.03      | ~ v2_pre_topc(sK3)
% 1.87/1.03      | ~ v8_pre_topc(sK3)
% 1.87/1.03      | ~ v2_lattice3(sK3)
% 1.87/1.03      | ~ v4_orders_2(X0)
% 1.87/1.03      | ~ v4_orders_2(sK3)
% 1.87/1.03      | ~ v7_waybel_0(X0)
% 1.87/1.03      | ~ l1_waybel_9(sK3)
% 1.87/1.03      | ~ v5_orders_2(sK3)
% 1.87/1.03      | ~ v1_lattice3(sK3)
% 1.87/1.03      | v2_struct_0(X0)
% 1.87/1.03      | ~ v3_orders_2(sK3) ),
% 1.87/1.03      inference(unflattening,[status(thm)],[c_633]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_638,plain,
% 1.87/1.03      ( v2_struct_0(X0)
% 1.87/1.03      | ~ v4_orders_2(X0)
% 1.87/1.03      | ~ r3_waybel_9(sK3,X0,X1)
% 1.87/1.03      | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
% 1.87/1.03      | r3_orders_2(sK3,X1,X2)
% 1.87/1.03      | ~ l1_waybel_0(X0,sK3)
% 1.87/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.87/1.03      | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
% 1.87/1.03      | ~ v7_waybel_0(X0) ),
% 1.87/1.03      inference(global_propositional_subsumption,
% 1.87/1.03                [status(thm)],
% 1.87/1.03                [c_634,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_32]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_639,plain,
% 1.87/1.03      ( ~ r3_waybel_9(sK3,X0,X1)
% 1.87/1.03      | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
% 1.87/1.03      | r3_orders_2(sK3,X1,X2)
% 1.87/1.03      | ~ l1_waybel_0(X0,sK3)
% 1.87/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/1.03      | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
% 1.87/1.03      | ~ v4_orders_2(X0)
% 1.87/1.03      | ~ v7_waybel_0(X0)
% 1.87/1.03      | v2_struct_0(X0) ),
% 1.87/1.03      inference(renaming,[status(thm)],[c_638]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_781,plain,
% 1.87/1.03      ( ~ r3_waybel_9(sK3,X0,X1)
% 1.87/1.03      | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
% 1.87/1.03      | r3_orders_2(sK3,X1,X2)
% 1.87/1.03      | ~ l1_waybel_0(X0,sK3)
% 1.87/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/1.03      | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
% 1.87/1.03      | ~ v4_orders_2(X0)
% 1.87/1.03      | v2_struct_0(X0)
% 1.87/1.03      | sK5 != X0 ),
% 1.87/1.03      inference(resolution_lifted,[status(thm)],[c_28,c_639]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_782,plain,
% 1.87/1.03      ( ~ r3_waybel_9(sK3,sK5,X0)
% 1.87/1.03      | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
% 1.87/1.03      | r3_orders_2(sK3,X0,X1)
% 1.87/1.03      | ~ l1_waybel_0(sK5,sK3)
% 1.87/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/1.03      | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
% 1.87/1.03      | ~ v4_orders_2(sK5)
% 1.87/1.03      | v2_struct_0(sK5) ),
% 1.87/1.03      inference(unflattening,[status(thm)],[c_781]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_786,plain,
% 1.87/1.03      ( r3_orders_2(sK3,X0,X1)
% 1.87/1.03      | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
% 1.87/1.03      | ~ r3_waybel_9(sK3,sK5,X0)
% 1.87/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/1.03      | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) ),
% 1.87/1.03      inference(global_propositional_subsumption,
% 1.87/1.03                [status(thm)],
% 1.87/1.03                [c_782,c_30,c_29,c_27]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_787,plain,
% 1.87/1.03      ( ~ r3_waybel_9(sK3,sK5,X0)
% 1.87/1.03      | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
% 1.87/1.03      | r3_orders_2(sK3,X0,X1)
% 1.87/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/1.03      | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) ),
% 1.87/1.03      inference(renaming,[status(thm)],[c_786]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_974,plain,
% 1.87/1.03      ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.87/1.03      | r3_orders_2(sK3,X1,X0)
% 1.87/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/1.03      | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
% 1.87/1.03      | sK4 != X1
% 1.87/1.03      | sK5 != sK5
% 1.87/1.03      | sK3 != sK3 ),
% 1.87/1.03      inference(resolution_lifted,[status(thm)],[c_24,c_787]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_975,plain,
% 1.87/1.03      ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.87/1.03      | r3_orders_2(sK3,sK4,X0)
% 1.87/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/1.03      | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 1.87/1.03      inference(unflattening,[status(thm)],[c_974]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_979,plain,
% 1.87/1.03      ( m1_subset_1(sK2(sK3),u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/1.03      | r3_orders_2(sK3,sK4,X0)
% 1.87/1.03      | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0) ),
% 1.87/1.03      inference(global_propositional_subsumption,
% 1.87/1.03                [status(thm)],
% 1.87/1.03                [c_975,c_31]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_980,plain,
% 1.87/1.03      ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.87/1.03      | r3_orders_2(sK3,sK4,X0)
% 1.87/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/1.03      | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) ),
% 1.87/1.03      inference(renaming,[status(thm)],[c_979]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_1052,plain,
% 1.87/1.03      ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.87/1.03      | r1_orders_2(sK3,X1,X2)
% 1.87/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.87/1.03      | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
% 1.87/1.03      | X0 != X2
% 1.87/1.03      | sK4 != X1
% 1.87/1.03      | sK3 != sK3 ),
% 1.87/1.03      inference(resolution_lifted,[status(thm)],[c_729,c_980]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_1053,plain,
% 1.87/1.03      ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.87/1.03      | r1_orders_2(sK3,sK4,X0)
% 1.87/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/1.03      | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 1.87/1.03      inference(unflattening,[status(thm)],[c_1052]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_1057,plain,
% 1.87/1.03      ( m1_subset_1(sK2(sK3),u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/1.03      | r1_orders_2(sK3,sK4,X0)
% 1.87/1.03      | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0) ),
% 1.87/1.03      inference(global_propositional_subsumption,
% 1.87/1.03                [status(thm)],
% 1.87/1.03                [c_1053,c_31]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_1058,plain,
% 1.87/1.03      ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.87/1.03      | r1_orders_2(sK3,sK4,X0)
% 1.87/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/1.03      | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) ),
% 1.87/1.03      inference(renaming,[status(thm)],[c_1057]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_2265,plain,
% 1.87/1.03      ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_68)
% 1.87/1.03      | r1_orders_2(sK3,sK4,X0_68)
% 1.87/1.03      | ~ m1_subset_1(X0_68,u1_struct_0(sK3))
% 1.87/1.03      | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) ),
% 1.87/1.03      inference(subtyping,[status(esa)],[c_1058]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_2343,plain,
% 1.87/1.03      ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_68) != iProver_top
% 1.87/1.03      | r1_orders_2(sK3,sK4,X0_68) = iProver_top
% 1.87/1.03      | m1_subset_1(X0_68,u1_struct_0(sK3)) != iProver_top
% 1.87/1.03      | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) = iProver_top ),
% 1.87/1.03      inference(predicate_to_equality,[status(thm)],[c_2265]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_2277,plain,
% 1.87/1.03      ( sP1_iProver_split | sP0_iProver_split ),
% 1.87/1.03      inference(splitting,
% 1.87/1.03                [splitting(split),new_symbols(definition,[])],
% 1.87/1.03                [c_2264]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_2346,plain,
% 1.87/1.03      ( sP1_iProver_split = iProver_top
% 1.87/1.03      | sP0_iProver_split = iProver_top ),
% 1.87/1.03      inference(predicate_to_equality,[status(thm)],[c_2277]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_2347,plain,
% 1.87/1.03      ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_68) != iProver_top
% 1.87/1.03      | r1_orders_2(sK3,sK4,X0_68) = iProver_top
% 1.87/1.03      | m1_subset_1(X0_68,u1_struct_0(sK3)) != iProver_top
% 1.87/1.03      | sP1_iProver_split != iProver_top ),
% 1.87/1.03      inference(predicate_to_equality,[status(thm)],[c_2276]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_2275,plain,
% 1.87/1.03      ( ~ m1_subset_1(X0_68,u1_struct_0(sK3))
% 1.87/1.03      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X0_68)
% 1.87/1.03      | ~ sP0_iProver_split ),
% 1.87/1.03      inference(splitting,
% 1.87/1.03                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.87/1.03                [c_2264]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_2712,plain,
% 1.87/1.03      ( k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X0_68)
% 1.87/1.03      | m1_subset_1(X0_68,u1_struct_0(sK3)) != iProver_top
% 1.87/1.03      | sP0_iProver_split != iProver_top ),
% 1.87/1.03      inference(predicate_to_equality,[status(thm)],[c_2275]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_3501,plain,
% 1.87/1.03      ( m1_subset_1(sK2(sK3),u1_struct_0(sK3)) != iProver_top
% 1.87/1.03      | sP0_iProver_split != iProver_top ),
% 1.87/1.03      inference(equality_resolution,[status(thm)],[c_2712]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_3546,plain,
% 1.87/1.03      ( m1_subset_1(X0_68,u1_struct_0(sK3)) != iProver_top
% 1.87/1.03      | r1_orders_2(sK3,sK4,X0_68) = iProver_top
% 1.87/1.03      | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_68) != iProver_top ),
% 1.87/1.03      inference(global_propositional_subsumption,
% 1.87/1.03                [status(thm)],
% 1.87/1.03                [c_2711,c_2343,c_2346,c_2347,c_3501]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_3547,plain,
% 1.87/1.03      ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_68) != iProver_top
% 1.87/1.03      | r1_orders_2(sK3,sK4,X0_68) = iProver_top
% 1.87/1.03      | m1_subset_1(X0_68,u1_struct_0(sK3)) != iProver_top ),
% 1.87/1.03      inference(renaming,[status(thm)],[c_3546]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_14,plain,
% 1.87/1.03      ( ~ l1_waybel_0(X0,X1)
% 1.87/1.03      | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.87/1.03      | ~ l1_struct_0(X1) ),
% 1.87/1.03      inference(cnf_transformation,[],[f67]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_18,plain,
% 1.87/1.03      ( ~ l1_waybel_9(X0) | l1_pre_topc(X0) ),
% 1.87/1.03      inference(cnf_transformation,[],[f70]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_2,plain,
% 1.87/1.03      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.87/1.03      inference(cnf_transformation,[],[f55]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_444,plain,
% 1.87/1.03      ( ~ l1_waybel_9(X0) | l1_struct_0(X0) ),
% 1.87/1.03      inference(resolution,[status(thm)],[c_18,c_2]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_458,plain,
% 1.87/1.03      ( ~ l1_waybel_0(X0,X1)
% 1.87/1.03      | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.87/1.03      | ~ l1_waybel_9(X2)
% 1.87/1.03      | X2 != X1 ),
% 1.87/1.03      inference(resolution_lifted,[status(thm)],[c_14,c_444]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_459,plain,
% 1.87/1.03      ( ~ l1_waybel_0(X0,X1)
% 1.87/1.03      | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.87/1.03      | ~ l1_waybel_9(X1) ),
% 1.87/1.03      inference(unflattening,[status(thm)],[c_458]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_699,plain,
% 1.87/1.03      ( ~ l1_waybel_0(X0,X1)
% 1.87/1.03      | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.87/1.03      | sK3 != X1 ),
% 1.87/1.03      inference(resolution_lifted,[status(thm)],[c_459,c_32]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_700,plain,
% 1.87/1.03      ( ~ l1_waybel_0(X0,sK3)
% 1.87/1.03      | m1_subset_1(u1_waybel_0(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) ),
% 1.87/1.03      inference(unflattening,[status(thm)],[c_699]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_867,plain,
% 1.87/1.03      ( m1_subset_1(u1_waybel_0(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
% 1.87/1.03      | sK5 != X0
% 1.87/1.03      | sK3 != sK3 ),
% 1.87/1.03      inference(resolution_lifted,[status(thm)],[c_27,c_700]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_868,plain,
% 1.87/1.03      ( m1_subset_1(u1_waybel_0(sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 1.87/1.03      inference(unflattening,[status(thm)],[c_867]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_2269,plain,
% 1.87/1.03      ( m1_subset_1(u1_waybel_0(sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 1.87/1.03      inference(subtyping,[status(esa)],[c_868]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_2705,plain,
% 1.87/1.03      ( m1_subset_1(u1_waybel_0(sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 1.87/1.03      inference(predicate_to_equality,[status(thm)],[c_2269]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_1,plain,
% 1.87/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.87/1.03      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 1.87/1.03      inference(cnf_transformation,[],[f54]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_2273,plain,
% 1.87/1.03      ( ~ m1_subset_1(X0_68,k1_zfmisc_1(k2_zfmisc_1(X0_71,X1_71)))
% 1.87/1.03      | k2_relset_1(X0_71,X1_71,X0_68) = k2_relat_1(X0_68) ),
% 1.87/1.03      inference(subtyping,[status(esa)],[c_1]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_2703,plain,
% 1.87/1.03      ( k2_relset_1(X0_71,X1_71,X0_68) = k2_relat_1(X0_68)
% 1.87/1.03      | m1_subset_1(X0_68,k1_zfmisc_1(k2_zfmisc_1(X0_71,X1_71))) != iProver_top ),
% 1.87/1.03      inference(predicate_to_equality,[status(thm)],[c_2273]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_2964,plain,
% 1.87/1.03      ( k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)) = k2_relat_1(u1_waybel_0(sK3,sK5)) ),
% 1.87/1.03      inference(superposition,[status(thm)],[c_2705,c_2703]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_3552,plain,
% 1.87/1.03      ( r2_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_68) != iProver_top
% 1.87/1.03      | r1_orders_2(sK3,sK4,X0_68) = iProver_top
% 1.87/1.03      | m1_subset_1(X0_68,u1_struct_0(sK3)) != iProver_top ),
% 1.87/1.03      inference(light_normalisation,[status(thm)],[c_3547,c_2964]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_3560,plain,
% 1.87/1.03      ( k1_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = X0_68
% 1.87/1.03      | r2_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_68) != iProver_top
% 1.87/1.03      | r1_orders_2(sK3,sK4,sK0(sK3,X0_68,k2_relat_1(u1_waybel_0(sK3,sK5)))) = iProver_top
% 1.87/1.03      | m1_subset_1(X0_68,u1_struct_0(sK3)) != iProver_top
% 1.87/1.03      | m1_subset_1(sK0(sK3,X0_68,k2_relat_1(u1_waybel_0(sK3,sK5))),u1_struct_0(sK3)) != iProver_top ),
% 1.87/1.03      inference(superposition,[status(thm)],[c_2716,c_3552]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_0,plain,
% 1.87/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.87/1.03      | v1_relat_1(X0) ),
% 1.87/1.03      inference(cnf_transformation,[],[f53]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_2274,plain,
% 1.87/1.03      ( ~ m1_subset_1(X0_68,k1_zfmisc_1(k2_zfmisc_1(X0_71,X1_71)))
% 1.87/1.03      | v1_relat_1(X0_68) ),
% 1.87/1.03      inference(subtyping,[status(esa)],[c_0]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_2702,plain,
% 1.87/1.03      ( m1_subset_1(X0_68,k1_zfmisc_1(k2_zfmisc_1(X0_71,X1_71))) != iProver_top
% 1.87/1.03      | v1_relat_1(X0_68) = iProver_top ),
% 1.87/1.03      inference(predicate_to_equality,[status(thm)],[c_2274]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_2959,plain,
% 1.87/1.03      ( v1_relat_1(u1_waybel_0(sK3,sK5)) = iProver_top ),
% 1.87/1.03      inference(superposition,[status(thm)],[c_2705,c_2702]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_16,plain,
% 1.87/1.03      ( v2_struct_0(X0)
% 1.87/1.03      | ~ l1_orders_2(X0)
% 1.87/1.03      | ~ v1_relat_1(X1)
% 1.87/1.03      | k1_yellow_0(X0,k2_relat_1(X1)) = k4_yellow_2(X0,X1) ),
% 1.87/1.03      inference(cnf_transformation,[],[f69]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_686,plain,
% 1.87/1.03      ( ~ v2_struct_0(X0) | ~ l1_orders_2(X0) | sK3 != X0 ),
% 1.87/1.03      inference(resolution_lifted,[status(thm)],[c_5,c_35]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_687,plain,
% 1.87/1.03      ( ~ v2_struct_0(sK3) | ~ l1_orders_2(sK3) ),
% 1.87/1.03      inference(unflattening,[status(thm)],[c_686]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_689,plain,
% 1.87/1.03      ( ~ v2_struct_0(sK3) ),
% 1.87/1.03      inference(global_propositional_subsumption,
% 1.87/1.03                [status(thm)],
% 1.87/1.03                [c_687,c_35,c_32,c_76,c_112]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_892,plain,
% 1.87/1.03      ( ~ l1_orders_2(X0)
% 1.87/1.03      | ~ v1_relat_1(X1)
% 1.87/1.03      | k1_yellow_0(X0,k2_relat_1(X1)) = k4_yellow_2(X0,X1)
% 1.87/1.03      | sK3 != X0 ),
% 1.87/1.03      inference(resolution_lifted,[status(thm)],[c_16,c_689]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_893,plain,
% 1.87/1.03      ( ~ l1_orders_2(sK3)
% 1.87/1.03      | ~ v1_relat_1(X0)
% 1.87/1.03      | k1_yellow_0(sK3,k2_relat_1(X0)) = k4_yellow_2(sK3,X0) ),
% 1.87/1.03      inference(unflattening,[status(thm)],[c_892]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_897,plain,
% 1.87/1.03      ( ~ v1_relat_1(X0)
% 1.87/1.03      | k1_yellow_0(sK3,k2_relat_1(X0)) = k4_yellow_2(sK3,X0) ),
% 1.87/1.03      inference(global_propositional_subsumption,
% 1.87/1.03                [status(thm)],
% 1.87/1.03                [c_893,c_32,c_76]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_2268,plain,
% 1.87/1.03      ( ~ v1_relat_1(X0_68)
% 1.87/1.03      | k1_yellow_0(sK3,k2_relat_1(X0_68)) = k4_yellow_2(sK3,X0_68) ),
% 1.87/1.03      inference(subtyping,[status(esa)],[c_897]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_2706,plain,
% 1.87/1.03      ( k1_yellow_0(sK3,k2_relat_1(X0_68)) = k4_yellow_2(sK3,X0_68)
% 1.87/1.03      | v1_relat_1(X0_68) != iProver_top ),
% 1.87/1.03      inference(predicate_to_equality,[status(thm)],[c_2268]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_3227,plain,
% 1.87/1.03      ( k1_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = k4_yellow_2(sK3,u1_waybel_0(sK3,sK5)) ),
% 1.87/1.03      inference(superposition,[status(thm)],[c_2959,c_2706]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_15,plain,
% 1.87/1.03      ( ~ l1_waybel_0(X0,X1)
% 1.87/1.03      | v2_struct_0(X1)
% 1.87/1.03      | ~ l1_orders_2(X1)
% 1.87/1.03      | k4_yellow_2(X1,u1_waybel_0(X1,X0)) = k1_waybel_2(X1,X0) ),
% 1.87/1.03      inference(cnf_transformation,[],[f68]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_859,plain,
% 1.87/1.03      ( v2_struct_0(X0)
% 1.87/1.03      | ~ l1_orders_2(X0)
% 1.87/1.03      | k4_yellow_2(X0,u1_waybel_0(X0,X1)) = k1_waybel_2(X0,X1)
% 1.87/1.03      | sK5 != X1
% 1.87/1.03      | sK3 != X0 ),
% 1.87/1.03      inference(resolution_lifted,[status(thm)],[c_15,c_27]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_860,plain,
% 1.87/1.03      ( v2_struct_0(sK3)
% 1.87/1.03      | ~ l1_orders_2(sK3)
% 1.87/1.03      | k4_yellow_2(sK3,u1_waybel_0(sK3,sK5)) = k1_waybel_2(sK3,sK5) ),
% 1.87/1.03      inference(unflattening,[status(thm)],[c_859]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_862,plain,
% 1.87/1.03      ( k4_yellow_2(sK3,u1_waybel_0(sK3,sK5)) = k1_waybel_2(sK3,sK5) ),
% 1.87/1.03      inference(global_propositional_subsumption,
% 1.87/1.03                [status(thm)],
% 1.87/1.03                [c_860,c_35,c_32,c_76,c_112]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_2270,plain,
% 1.87/1.03      ( k4_yellow_2(sK3,u1_waybel_0(sK3,sK5)) = k1_waybel_2(sK3,sK5) ),
% 1.87/1.03      inference(subtyping,[status(esa)],[c_862]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_3228,plain,
% 1.87/1.03      ( k1_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = k1_waybel_2(sK3,sK5) ),
% 1.87/1.03      inference(light_normalisation,[status(thm)],[c_3227,c_2270]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_3578,plain,
% 1.87/1.03      ( k1_waybel_2(sK3,sK5) = X0_68
% 1.87/1.03      | r2_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_68) != iProver_top
% 1.87/1.03      | r1_orders_2(sK3,sK4,sK0(sK3,X0_68,k2_relat_1(u1_waybel_0(sK3,sK5)))) = iProver_top
% 1.87/1.03      | m1_subset_1(X0_68,u1_struct_0(sK3)) != iProver_top
% 1.87/1.03      | m1_subset_1(sK0(sK3,X0_68,k2_relat_1(u1_waybel_0(sK3,sK5))),u1_struct_0(sK3)) != iProver_top ),
% 1.87/1.03      inference(demodulation,[status(thm)],[c_3560,c_3228]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_3828,plain,
% 1.87/1.03      ( k1_waybel_2(sK3,sK5) = X0_68
% 1.87/1.03      | k1_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = X0_68
% 1.87/1.03      | r2_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_68) != iProver_top
% 1.87/1.03      | r1_orders_2(sK3,sK4,sK0(sK3,X0_68,k2_relat_1(u1_waybel_0(sK3,sK5)))) = iProver_top
% 1.87/1.03      | m1_subset_1(X0_68,u1_struct_0(sK3)) != iProver_top ),
% 1.87/1.03      inference(superposition,[status(thm)],[c_2715,c_3578]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_3834,plain,
% 1.87/1.03      ( k1_waybel_2(sK3,sK5) = X0_68
% 1.87/1.03      | r2_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_68) != iProver_top
% 1.87/1.03      | r1_orders_2(sK3,sK4,sK0(sK3,X0_68,k2_relat_1(u1_waybel_0(sK3,sK5)))) = iProver_top
% 1.87/1.03      | m1_subset_1(X0_68,u1_struct_0(sK3)) != iProver_top ),
% 1.87/1.03      inference(demodulation,[status(thm)],[c_3828,c_3228]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_9,plain,
% 1.87/1.03      ( ~ r2_lattice3(X0,X1,X2)
% 1.87/1.03      | ~ r1_orders_2(X0,X2,sK0(X0,X2,X1))
% 1.87/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.87/1.03      | ~ v5_orders_2(X0)
% 1.87/1.03      | ~ l1_orders_2(X0)
% 1.87/1.03      | k1_yellow_0(X0,X1) = X2 ),
% 1.87/1.03      inference(cnf_transformation,[],[f63]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_1210,plain,
% 1.87/1.03      ( ~ r2_lattice3(X0,X1,X2)
% 1.87/1.03      | ~ r1_orders_2(X0,X2,sK0(X0,X2,X1))
% 1.87/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.87/1.03      | ~ l1_orders_2(X0)
% 1.87/1.03      | k1_yellow_0(X0,X1) = X2
% 1.87/1.03      | sK3 != X0 ),
% 1.87/1.03      inference(resolution_lifted,[status(thm)],[c_9,c_36]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_1211,plain,
% 1.87/1.03      ( ~ r2_lattice3(sK3,X0,X1)
% 1.87/1.03      | ~ r1_orders_2(sK3,X1,sK0(sK3,X1,X0))
% 1.87/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/1.03      | ~ l1_orders_2(sK3)
% 1.87/1.03      | k1_yellow_0(sK3,X0) = X1 ),
% 1.87/1.03      inference(unflattening,[status(thm)],[c_1210]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_1215,plain,
% 1.87/1.03      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/1.03      | ~ r1_orders_2(sK3,X1,sK0(sK3,X1,X0))
% 1.87/1.03      | ~ r2_lattice3(sK3,X0,X1)
% 1.87/1.03      | k1_yellow_0(sK3,X0) = X1 ),
% 1.87/1.03      inference(global_propositional_subsumption,
% 1.87/1.03                [status(thm)],
% 1.87/1.03                [c_1211,c_32,c_76]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_1216,plain,
% 1.87/1.03      ( ~ r2_lattice3(sK3,X0,X1)
% 1.87/1.03      | ~ r1_orders_2(sK3,X1,sK0(sK3,X1,X0))
% 1.87/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/1.03      | k1_yellow_0(sK3,X0) = X1 ),
% 1.87/1.03      inference(renaming,[status(thm)],[c_1215]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_2259,plain,
% 1.87/1.03      ( ~ r2_lattice3(sK3,X0_70,X0_68)
% 1.87/1.03      | ~ r1_orders_2(sK3,X0_68,sK0(sK3,X0_68,X0_70))
% 1.87/1.03      | ~ m1_subset_1(X0_68,u1_struct_0(sK3))
% 1.87/1.03      | k1_yellow_0(sK3,X0_70) = X0_68 ),
% 1.87/1.03      inference(subtyping,[status(esa)],[c_1216]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_2717,plain,
% 1.87/1.03      ( k1_yellow_0(sK3,X0_70) = X0_68
% 1.87/1.03      | r2_lattice3(sK3,X0_70,X0_68) != iProver_top
% 1.87/1.03      | r1_orders_2(sK3,X0_68,sK0(sK3,X0_68,X0_70)) != iProver_top
% 1.87/1.03      | m1_subset_1(X0_68,u1_struct_0(sK3)) != iProver_top ),
% 1.87/1.03      inference(predicate_to_equality,[status(thm)],[c_2259]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_3848,plain,
% 1.87/1.03      ( k1_waybel_2(sK3,sK5) = sK4
% 1.87/1.03      | k1_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = sK4
% 1.87/1.03      | r2_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),sK4) != iProver_top
% 1.87/1.03      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 1.87/1.03      inference(superposition,[status(thm)],[c_3834,c_2717]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_3853,plain,
% 1.87/1.03      ( k1_waybel_2(sK3,sK5) = sK4
% 1.87/1.03      | r2_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),sK4) != iProver_top
% 1.87/1.03      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 1.87/1.03      inference(demodulation,[status(thm)],[c_3848,c_3228]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_19,plain,
% 1.87/1.03      ( ~ v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0)
% 1.87/1.03      | ~ r3_waybel_9(X0,X1,X2)
% 1.87/1.03      | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
% 1.87/1.03      | ~ v10_waybel_0(X1,X0)
% 1.87/1.03      | ~ l1_waybel_0(X1,X0)
% 1.87/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.87/1.03      | ~ v2_pre_topc(X0)
% 1.87/1.03      | ~ v8_pre_topc(X0)
% 1.87/1.03      | ~ v2_lattice3(X0)
% 1.87/1.03      | ~ v1_compts_1(X0)
% 1.87/1.03      | ~ v4_orders_2(X1)
% 1.87/1.03      | ~ v4_orders_2(X0)
% 1.87/1.03      | ~ v7_waybel_0(X1)
% 1.87/1.03      | ~ l1_waybel_9(X0)
% 1.87/1.03      | ~ v5_orders_2(X0)
% 1.87/1.03      | ~ v1_lattice3(X0)
% 1.87/1.03      | v2_struct_0(X1)
% 1.87/1.03      | ~ v3_orders_2(X0) ),
% 1.87/1.03      inference(cnf_transformation,[],[f96]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_25,negated_conjecture,
% 1.87/1.03      ( v10_waybel_0(sK5,sK3) ),
% 1.87/1.03      inference(cnf_transformation,[],[f91]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_523,plain,
% 1.87/1.03      ( ~ v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0)
% 1.87/1.03      | ~ r3_waybel_9(X0,X1,X2)
% 1.87/1.03      | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
% 1.87/1.03      | ~ l1_waybel_0(X1,X0)
% 1.87/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.87/1.03      | ~ v2_pre_topc(X0)
% 1.87/1.03      | ~ v8_pre_topc(X0)
% 1.87/1.03      | ~ v2_lattice3(X0)
% 1.87/1.03      | ~ v1_compts_1(X0)
% 1.87/1.03      | ~ v4_orders_2(X1)
% 1.87/1.03      | ~ v4_orders_2(X0)
% 1.87/1.03      | ~ v7_waybel_0(X1)
% 1.87/1.03      | ~ l1_waybel_9(X0)
% 1.87/1.03      | ~ v5_orders_2(X0)
% 1.87/1.03      | ~ v1_lattice3(X0)
% 1.87/1.03      | v2_struct_0(X1)
% 1.87/1.03      | ~ v3_orders_2(X0)
% 1.87/1.03      | sK5 != X1
% 1.87/1.03      | sK3 != X0 ),
% 1.87/1.03      inference(resolution_lifted,[status(thm)],[c_19,c_25]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_524,plain,
% 1.87/1.03      ( ~ v5_pre_topc(k4_waybel_1(sK3,sK1(sK3)),sK3,sK3)
% 1.87/1.03      | ~ r3_waybel_9(sK3,sK5,X0)
% 1.87/1.03      | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.87/1.03      | ~ l1_waybel_0(sK5,sK3)
% 1.87/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/1.03      | ~ v2_pre_topc(sK3)
% 1.87/1.03      | ~ v8_pre_topc(sK3)
% 1.87/1.03      | ~ v2_lattice3(sK3)
% 1.87/1.03      | ~ v1_compts_1(sK3)
% 1.87/1.03      | ~ v4_orders_2(sK5)
% 1.87/1.03      | ~ v4_orders_2(sK3)
% 1.87/1.03      | ~ v7_waybel_0(sK5)
% 1.87/1.03      | ~ l1_waybel_9(sK3)
% 1.87/1.03      | ~ v5_orders_2(sK3)
% 1.87/1.03      | ~ v1_lattice3(sK3)
% 1.87/1.03      | v2_struct_0(sK5)
% 1.87/1.03      | ~ v3_orders_2(sK3) ),
% 1.87/1.03      inference(unflattening,[status(thm)],[c_523]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_528,plain,
% 1.87/1.03      ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.87/1.03      | ~ r3_waybel_9(sK3,sK5,X0)
% 1.87/1.03      | ~ v5_pre_topc(k4_waybel_1(sK3,sK1(sK3)),sK3,sK3)
% 1.87/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 1.87/1.03      inference(global_propositional_subsumption,
% 1.87/1.03                [status(thm)],
% 1.87/1.03                [c_524,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_30,
% 1.87/1.03                 c_29,c_28,c_27]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_529,plain,
% 1.87/1.03      ( ~ v5_pre_topc(k4_waybel_1(sK3,sK1(sK3)),sK3,sK3)
% 1.87/1.03      | ~ r3_waybel_9(sK3,sK5,X0)
% 1.87/1.03      | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.87/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 1.87/1.03      inference(renaming,[status(thm)],[c_528]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_602,plain,
% 1.87/1.03      ( ~ r3_waybel_9(sK3,sK5,X0)
% 1.87/1.03      | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.87/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/1.03      | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X1)
% 1.87/1.03      | sK3 != sK3 ),
% 1.87/1.03      inference(resolution_lifted,[status(thm)],[c_26,c_529]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_998,plain,
% 1.87/1.03      ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.87/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/1.03      | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X1)
% 1.87/1.03      | sK4 != X0
% 1.87/1.03      | sK5 != sK5
% 1.87/1.03      | sK3 != sK3 ),
% 1.87/1.03      inference(resolution_lifted,[status(thm)],[c_24,c_602]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_999,plain,
% 1.87/1.03      ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
% 1.87/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 1.87/1.03      | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0) ),
% 1.87/1.03      inference(unflattening,[status(thm)],[c_998]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_1003,plain,
% 1.87/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/1.03      | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
% 1.87/1.03      | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0) ),
% 1.87/1.03      inference(global_propositional_subsumption,
% 1.87/1.03                [status(thm)],
% 1.87/1.03                [c_999,c_31]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_1004,plain,
% 1.87/1.03      ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
% 1.87/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/1.03      | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0) ),
% 1.87/1.03      inference(renaming,[status(thm)],[c_1003]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_2267,plain,
% 1.87/1.03      ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
% 1.87/1.03      | ~ m1_subset_1(X0_68,u1_struct_0(sK3))
% 1.87/1.03      | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0_68) ),
% 1.87/1.03      inference(subtyping,[status(esa)],[c_1004]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_2707,plain,
% 1.87/1.03      ( k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0_68)
% 1.87/1.03      | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) = iProver_top
% 1.87/1.03      | m1_subset_1(X0_68,u1_struct_0(sK3)) != iProver_top ),
% 1.87/1.03      inference(predicate_to_equality,[status(thm)],[c_2267]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_20,plain,
% 1.87/1.03      ( ~ r3_waybel_9(X0,X1,X2)
% 1.87/1.03      | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
% 1.87/1.03      | ~ v10_waybel_0(X1,X0)
% 1.87/1.03      | ~ l1_waybel_0(X1,X0)
% 1.87/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.87/1.03      | m1_subset_1(sK1(X0),u1_struct_0(X0))
% 1.87/1.03      | ~ v2_pre_topc(X0)
% 1.87/1.03      | ~ v8_pre_topc(X0)
% 1.87/1.03      | ~ v2_lattice3(X0)
% 1.87/1.03      | ~ v1_compts_1(X0)
% 1.87/1.03      | ~ v4_orders_2(X1)
% 1.87/1.03      | ~ v4_orders_2(X0)
% 1.87/1.03      | ~ v7_waybel_0(X1)
% 1.87/1.03      | ~ l1_waybel_9(X0)
% 1.87/1.03      | ~ v5_orders_2(X0)
% 1.87/1.03      | ~ v1_lattice3(X0)
% 1.87/1.03      | v2_struct_0(X1)
% 1.87/1.03      | ~ v3_orders_2(X0) ),
% 1.87/1.03      inference(cnf_transformation,[],[f97]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_499,plain,
% 1.87/1.03      ( ~ r3_waybel_9(X0,X1,X2)
% 1.87/1.03      | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
% 1.87/1.03      | ~ l1_waybel_0(X1,X0)
% 1.87/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.87/1.03      | m1_subset_1(sK1(X0),u1_struct_0(X0))
% 1.87/1.03      | ~ v2_pre_topc(X0)
% 1.87/1.03      | ~ v8_pre_topc(X0)
% 1.87/1.03      | ~ v2_lattice3(X0)
% 1.87/1.03      | ~ v1_compts_1(X0)
% 1.87/1.03      | ~ v4_orders_2(X1)
% 1.87/1.03      | ~ v4_orders_2(X0)
% 1.87/1.03      | ~ v7_waybel_0(X1)
% 1.87/1.03      | ~ l1_waybel_9(X0)
% 1.87/1.03      | ~ v5_orders_2(X0)
% 1.87/1.03      | ~ v1_lattice3(X0)
% 1.87/1.03      | v2_struct_0(X1)
% 1.87/1.03      | ~ v3_orders_2(X0)
% 1.87/1.03      | sK5 != X1
% 1.87/1.03      | sK3 != X0 ),
% 1.87/1.03      inference(resolution_lifted,[status(thm)],[c_20,c_25]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_500,plain,
% 1.87/1.03      ( ~ r3_waybel_9(sK3,sK5,X0)
% 1.87/1.03      | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.87/1.03      | ~ l1_waybel_0(sK5,sK3)
% 1.87/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/1.03      | m1_subset_1(sK1(sK3),u1_struct_0(sK3))
% 1.87/1.03      | ~ v2_pre_topc(sK3)
% 1.87/1.03      | ~ v8_pre_topc(sK3)
% 1.87/1.03      | ~ v2_lattice3(sK3)
% 1.87/1.03      | ~ v1_compts_1(sK3)
% 1.87/1.03      | ~ v4_orders_2(sK5)
% 1.87/1.03      | ~ v4_orders_2(sK3)
% 1.87/1.03      | ~ v7_waybel_0(sK5)
% 1.87/1.03      | ~ l1_waybel_9(sK3)
% 1.87/1.03      | ~ v5_orders_2(sK3)
% 1.87/1.03      | ~ v1_lattice3(sK3)
% 1.87/1.03      | v2_struct_0(sK5)
% 1.87/1.03      | ~ v3_orders_2(sK3) ),
% 1.87/1.03      inference(unflattening,[status(thm)],[c_499]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_504,plain,
% 1.87/1.03      ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.87/1.03      | ~ r3_waybel_9(sK3,sK5,X0)
% 1.87/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/1.03      | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) ),
% 1.87/1.03      inference(global_propositional_subsumption,
% 1.87/1.03                [status(thm)],
% 1.87/1.03                [c_500,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_30,
% 1.87/1.03                 c_29,c_28,c_27]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_505,plain,
% 1.87/1.03      ( ~ r3_waybel_9(sK3,sK5,X0)
% 1.87/1.03      | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.87/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/1.03      | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) ),
% 1.87/1.03      inference(renaming,[status(thm)],[c_504]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_1019,plain,
% 1.87/1.03      ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.87/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/1.03      | m1_subset_1(sK1(sK3),u1_struct_0(sK3))
% 1.87/1.03      | sK4 != X0
% 1.87/1.03      | sK5 != sK5
% 1.87/1.03      | sK3 != sK3 ),
% 1.87/1.03      inference(resolution_lifted,[status(thm)],[c_24,c_505]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_1020,plain,
% 1.87/1.03      ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
% 1.87/1.03      | m1_subset_1(sK1(sK3),u1_struct_0(sK3))
% 1.87/1.03      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 1.87/1.03      inference(unflattening,[status(thm)],[c_1019]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_1022,plain,
% 1.87/1.03      ( m1_subset_1(sK1(sK3),u1_struct_0(sK3))
% 1.87/1.03      | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) ),
% 1.87/1.03      inference(global_propositional_subsumption,
% 1.87/1.03                [status(thm)],
% 1.87/1.03                [c_1020,c_31]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_1023,plain,
% 1.87/1.03      ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
% 1.87/1.03      | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) ),
% 1.87/1.03      inference(renaming,[status(thm)],[c_1022]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_1024,plain,
% 1.87/1.03      ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) = iProver_top
% 1.87/1.03      | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) = iProver_top ),
% 1.87/1.03      inference(predicate_to_equality,[status(thm)],[c_1023]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_2283,plain,( X0_72 = X0_72 ),theory(equality) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_2898,plain,
% 1.87/1.03      ( k4_waybel_1(sK3,sK1(sK3)) = k4_waybel_1(sK3,sK1(sK3)) ),
% 1.87/1.03      inference(instantiation,[status(thm)],[c_2283]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_2899,plain,
% 1.87/1.03      ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
% 1.87/1.03      | ~ m1_subset_1(sK1(sK3),u1_struct_0(sK3))
% 1.87/1.03      | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,sK1(sK3)) ),
% 1.87/1.03      inference(instantiation,[status(thm)],[c_2267]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_2900,plain,
% 1.87/1.03      ( k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,sK1(sK3))
% 1.87/1.03      | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) = iProver_top
% 1.87/1.03      | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) != iProver_top ),
% 1.87/1.03      inference(predicate_to_equality,[status(thm)],[c_2899]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_2910,plain,
% 1.87/1.03      ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) = iProver_top ),
% 1.87/1.03      inference(global_propositional_subsumption,
% 1.87/1.03                [status(thm)],
% 1.87/1.03                [c_2707,c_1024,c_2898,c_2900]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_3017,plain,
% 1.87/1.03      ( r2_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),sK4) = iProver_top ),
% 1.87/1.03      inference(demodulation,[status(thm)],[c_2964,c_2910]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_23,negated_conjecture,
% 1.87/1.03      ( k1_waybel_2(sK3,sK5) != sK4 ),
% 1.87/1.03      inference(cnf_transformation,[],[f93]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_2272,negated_conjecture,
% 1.87/1.03      ( k1_waybel_2(sK3,sK5) != sK4 ),
% 1.87/1.03      inference(subtyping,[status(esa)],[c_23]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(c_50,plain,
% 1.87/1.03      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 1.87/1.03      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 1.87/1.03  
% 1.87/1.03  cnf(contradiction,plain,
% 1.87/1.03      ( $false ),
% 1.87/1.03      inference(minisat,[status(thm)],[c_3853,c_3017,c_2272,c_50]) ).
% 1.87/1.03  
% 1.87/1.03  
% 1.87/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 1.87/1.03  
% 1.87/1.03  ------                               Statistics
% 1.87/1.03  
% 1.87/1.03  ------ General
% 1.87/1.03  
% 1.87/1.03  abstr_ref_over_cycles:                  0
% 1.87/1.03  abstr_ref_under_cycles:                 0
% 1.87/1.03  gc_basic_clause_elim:                   0
% 1.87/1.03  forced_gc_time:                         0
% 1.87/1.03  parsing_time:                           0.024
% 1.87/1.03  unif_index_cands_time:                  0.
% 1.87/1.03  unif_index_add_time:                    0.
% 1.87/1.03  orderings_time:                         0.
% 1.87/1.03  out_proof_time:                         0.018
% 1.87/1.03  total_time:                             0.185
% 1.87/1.03  num_of_symbols:                         76
% 1.87/1.03  num_of_terms:                           2472
% 1.87/1.03  
% 1.87/1.03  ------ Preprocessing
% 1.87/1.03  
% 1.87/1.03  num_of_splits:                          2
% 1.87/1.03  num_of_split_atoms:                     2
% 1.87/1.03  num_of_reused_defs:                     0
% 1.87/1.03  num_eq_ax_congr_red:                    31
% 1.87/1.03  num_of_sem_filtered_clauses:            1
% 1.87/1.04  num_of_subtypes:                        6
% 1.87/1.04  monotx_restored_types:                  0
% 1.87/1.04  sat_num_of_epr_types:                   0
% 1.87/1.04  sat_num_of_non_cyclic_types:            0
% 1.87/1.04  sat_guarded_non_collapsed_types:        1
% 1.87/1.04  num_pure_diseq_elim:                    0
% 1.87/1.04  simp_replaced_by:                       0
% 1.87/1.04  res_preprocessed:                       158
% 1.87/1.04  prep_upred:                             0
% 1.87/1.04  prep_unflattend:                        60
% 1.87/1.04  smt_new_axioms:                         0
% 1.87/1.04  pred_elim_cands:                        5
% 1.87/1.04  pred_elim:                              19
% 1.87/1.04  pred_elim_cl:                           21
% 1.87/1.04  pred_elim_cycles:                       27
% 1.87/1.04  merged_defs:                            0
% 1.87/1.04  merged_defs_ncl:                        0
% 1.87/1.04  bin_hyper_res:                          0
% 1.87/1.04  prep_cycles:                            4
% 1.87/1.04  pred_elim_time:                         0.041
% 1.87/1.04  splitting_time:                         0.
% 1.87/1.04  sem_filter_time:                        0.
% 1.87/1.04  monotx_time:                            0.
% 1.87/1.04  subtype_inf_time:                       0.
% 1.87/1.04  
% 1.87/1.04  ------ Problem properties
% 1.87/1.04  
% 1.87/1.04  clauses:                                22
% 1.87/1.04  conjectures:                            2
% 1.87/1.04  epr:                                    1
% 1.87/1.04  horn:                                   15
% 1.87/1.04  ground:                                 6
% 1.87/1.04  unary:                                  4
% 1.87/1.04  binary:                                 5
% 1.87/1.04  lits:                                   63
% 1.87/1.04  lits_eq:                                11
% 1.87/1.04  fd_pure:                                0
% 1.87/1.04  fd_pseudo:                              0
% 1.87/1.04  fd_cond:                                0
% 1.87/1.04  fd_pseudo_cond:                         3
% 1.87/1.04  ac_symbols:                             0
% 1.87/1.04  
% 1.87/1.04  ------ Propositional Solver
% 1.87/1.04  
% 1.87/1.04  prop_solver_calls:                      26
% 1.87/1.04  prop_fast_solver_calls:                 1644
% 1.87/1.04  smt_solver_calls:                       0
% 1.87/1.04  smt_fast_solver_calls:                  0
% 1.87/1.04  prop_num_of_clauses:                    902
% 1.87/1.04  prop_preprocess_simplified:             4735
% 1.87/1.04  prop_fo_subsumed:                       87
% 1.87/1.04  prop_solver_time:                       0.
% 1.87/1.04  smt_solver_time:                        0.
% 1.87/1.04  smt_fast_solver_time:                   0.
% 1.87/1.04  prop_fast_solver_time:                  0.
% 1.87/1.04  prop_unsat_core_time:                   0.
% 1.87/1.04  
% 1.87/1.04  ------ QBF
% 1.87/1.04  
% 1.87/1.04  qbf_q_res:                              0
% 1.87/1.04  qbf_num_tautologies:                    0
% 1.87/1.04  qbf_prep_cycles:                        0
% 1.87/1.04  
% 1.87/1.04  ------ BMC1
% 1.87/1.04  
% 1.87/1.04  bmc1_current_bound:                     -1
% 1.87/1.04  bmc1_last_solved_bound:                 -1
% 1.87/1.04  bmc1_unsat_core_size:                   -1
% 1.87/1.04  bmc1_unsat_core_parents_size:           -1
% 1.87/1.04  bmc1_merge_next_fun:                    0
% 1.87/1.04  bmc1_unsat_core_clauses_time:           0.
% 1.87/1.04  
% 1.87/1.04  ------ Instantiation
% 1.87/1.04  
% 1.87/1.04  inst_num_of_clauses:                    208
% 1.87/1.04  inst_num_in_passive:                    52
% 1.87/1.04  inst_num_in_active:                     147
% 1.87/1.04  inst_num_in_unprocessed:                9
% 1.87/1.04  inst_num_of_loops:                      160
% 1.87/1.04  inst_num_of_learning_restarts:          0
% 1.87/1.04  inst_num_moves_active_passive:          10
% 1.87/1.04  inst_lit_activity:                      0
% 1.87/1.04  inst_lit_activity_moves:                0
% 1.87/1.04  inst_num_tautologies:                   0
% 1.87/1.04  inst_num_prop_implied:                  0
% 1.87/1.04  inst_num_existing_simplified:           0
% 1.87/1.04  inst_num_eq_res_simplified:             0
% 1.87/1.04  inst_num_child_elim:                    0
% 1.87/1.04  inst_num_of_dismatching_blockings:      18
% 1.87/1.04  inst_num_of_non_proper_insts:           152
% 1.87/1.04  inst_num_of_duplicates:                 0
% 1.87/1.04  inst_inst_num_from_inst_to_res:         0
% 1.87/1.04  inst_dismatching_checking_time:         0.
% 1.87/1.04  
% 1.87/1.04  ------ Resolution
% 1.87/1.04  
% 1.87/1.04  res_num_of_clauses:                     0
% 1.87/1.04  res_num_in_passive:                     0
% 1.87/1.04  res_num_in_active:                      0
% 1.87/1.04  res_num_of_loops:                       162
% 1.87/1.04  res_forward_subset_subsumed:            34
% 1.87/1.04  res_backward_subset_subsumed:           0
% 1.87/1.04  res_forward_subsumed:                   0
% 1.87/1.04  res_backward_subsumed:                  0
% 1.87/1.04  res_forward_subsumption_resolution:     2
% 1.87/1.04  res_backward_subsumption_resolution:    0
% 1.87/1.04  res_clause_to_clause_subsumption:       172
% 1.87/1.04  res_orphan_elimination:                 0
% 1.87/1.04  res_tautology_del:                      20
% 1.87/1.04  res_num_eq_res_simplified:              0
% 1.87/1.04  res_num_sel_changes:                    0
% 1.87/1.04  res_moves_from_active_to_pass:          0
% 1.87/1.04  
% 1.87/1.04  ------ Superposition
% 1.87/1.04  
% 1.87/1.04  sup_time_total:                         0.
% 1.87/1.04  sup_time_generating:                    0.
% 1.87/1.04  sup_time_sim_full:                      0.
% 1.87/1.04  sup_time_sim_immed:                     0.
% 1.87/1.04  
% 1.87/1.04  sup_num_of_clauses:                     37
% 1.87/1.04  sup_num_in_active:                      29
% 1.87/1.04  sup_num_in_passive:                     8
% 1.87/1.04  sup_num_of_loops:                       31
% 1.87/1.04  sup_fw_superposition:                   16
% 1.87/1.04  sup_bw_superposition:                   7
% 1.87/1.04  sup_immediate_simplified:               13
% 1.87/1.04  sup_given_eliminated:                   0
% 1.87/1.04  comparisons_done:                       0
% 1.87/1.04  comparisons_avoided:                    0
% 1.87/1.04  
% 1.87/1.04  ------ Simplifications
% 1.87/1.04  
% 1.87/1.04  
% 1.87/1.04  sim_fw_subset_subsumed:                 0
% 1.87/1.04  sim_bw_subset_subsumed:                 6
% 1.87/1.04  sim_fw_subsumed:                        2
% 1.87/1.04  sim_bw_subsumed:                        1
% 1.87/1.04  sim_fw_subsumption_res:                 1
% 1.87/1.04  sim_bw_subsumption_res:                 0
% 1.87/1.04  sim_tautology_del:                      1
% 1.87/1.04  sim_eq_tautology_del:                   0
% 1.87/1.04  sim_eq_res_simp:                        0
% 1.87/1.04  sim_fw_demodulated:                     6
% 1.87/1.04  sim_bw_demodulated:                     1
% 1.87/1.04  sim_light_normalised:                   5
% 1.87/1.04  sim_joinable_taut:                      0
% 1.87/1.04  sim_joinable_simp:                      0
% 1.87/1.04  sim_ac_normalised:                      0
% 1.87/1.04  sim_smt_subsumption:                    0
% 1.87/1.04  
%------------------------------------------------------------------------------
