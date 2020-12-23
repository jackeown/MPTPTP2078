%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:58 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :  257 (2599 expanded)
%              Number of clauses        :  166 ( 567 expanded)
%              Number of leaves         :   20 ( 837 expanded)
%              Depth                    :   38
%              Number of atoms          : 1603 (36716 expanded)
%              Number of equality atoms :  235 (2521 expanded)
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
    inference(ennf_transformation,[],[f15])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r2_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X1,sK0(X0,X1,X2))
        & r2_lattice3(X0,X2,sK0(X0,X1,X2))
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f43])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X2) = X1
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

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
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f52,plain,(
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

fof(f51,plain,(
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

fof(f50,plain,
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

fof(f53,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f41,f52,f51,f50])).

fof(f80,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f84,plain,(
    l1_waybel_9(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => ( l1_orders_2(X0)
        & l1_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => l1_orders_2(X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f35,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f71,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X2) = X1
      | r2_lattice3(X0,X2,sK0(X0,X1,X2))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

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

fof(f42,plain,(
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

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f78,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f82,plain,(
    v2_lattice3(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f92,plain,(
    r3_waybel_9(sK3,sK5,sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f88,plain,(
    v7_waybel_0(sK5) ),
    inference(cnf_transformation,[],[f53])).

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
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

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
    inference(rectify,[],[f39])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X5] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X5),X0,X0)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0)
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f47,f48])).

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
    inference(cnf_transformation,[],[f49])).

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
    inference(cnf_transformation,[],[f53])).

fof(f76,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f77,plain,(
    v8_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f79,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f81,plain,(
    v1_lattice3(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f83,plain,(
    v1_compts_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f86,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f87,plain,(
    v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f89,plain,(
    l1_waybel_0(sK5,sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f85,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f53])).

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
    inference(cnf_transformation,[],[f49])).

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

fof(f18,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f56,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_yellow_0(X0,k2_relat_1(X1)) = k4_yellow_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_yellow_0(X0,k2_relat_1(X1)) = k4_yellow_2(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_yellow_0(X0,k2_relat_1(X1)) = k4_yellow_2(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_yellow_0(X0,k2_relat_1(X1)) = k4_yellow_2(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1))
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1))
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X2) = X1
      | ~ r1_orders_2(X0,X1,sK0(X0,X1,X2))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

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
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X4] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0)
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f45])).

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
    inference(cnf_transformation,[],[f46])).

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
    inference(cnf_transformation,[],[f53])).

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
    inference(cnf_transformation,[],[f46])).

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
    inference(cnf_transformation,[],[f53])).

cnf(c_11,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_35,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1125,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X2,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_35])).

cnf(c_1126,plain,
    ( ~ r2_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK0(sK3,X1,X0),u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | k1_yellow_0(sK3,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1125])).

cnf(c_31,negated_conjecture,
    ( l1_waybel_9(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_17,plain,
    ( ~ l1_waybel_9(X0)
    | l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_72,plain,
    ( ~ l1_waybel_9(sK3)
    | l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1130,plain,
    ( m1_subset_1(sK0(sK3,X1,X0),u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r2_lattice3(sK3,X0,X1)
    | k1_yellow_0(sK3,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1126,c_31,c_72])).

cnf(c_1131,plain,
    ( ~ r2_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK0(sK3,X1,X0),u1_struct_0(sK3))
    | k1_yellow_0(sK3,X0) = X1 ),
    inference(renaming,[status(thm)],[c_1130])).

cnf(c_2224,plain,
    ( ~ r2_lattice3(sK3,X0_69,X0_67)
    | ~ m1_subset_1(X0_67,u1_struct_0(sK3))
    | m1_subset_1(sK0(sK3,X0_67,X0_69),u1_struct_0(sK3))
    | k1_yellow_0(sK3,X0_69) = X0_67 ),
    inference(subtyping,[status(esa)],[c_1131])).

cnf(c_2678,plain,
    ( k1_yellow_0(sK3,X0_69) = X0_67
    | r2_lattice3(sK3,X0_69,X0_67) != iProver_top
    | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK0(sK3,X0_67,X0_69),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2224])).

cnf(c_10,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK0(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1149,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK0(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_35])).

cnf(c_1150,plain,
    ( ~ r2_lattice3(sK3,X0,X1)
    | r2_lattice3(sK3,X0,sK0(sK3,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | k1_yellow_0(sK3,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1149])).

cnf(c_1154,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_lattice3(sK3,X0,sK0(sK3,X1,X0))
    | ~ r2_lattice3(sK3,X0,X1)
    | k1_yellow_0(sK3,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1150,c_31,c_72])).

cnf(c_1155,plain,
    ( ~ r2_lattice3(sK3,X0,X1)
    | r2_lattice3(sK3,X0,sK0(sK3,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k1_yellow_0(sK3,X0) = X1 ),
    inference(renaming,[status(thm)],[c_1154])).

cnf(c_2223,plain,
    ( ~ r2_lattice3(sK3,X0_69,X0_67)
    | r2_lattice3(sK3,X0_69,sK0(sK3,X0_67,X0_69))
    | ~ m1_subset_1(X0_67,u1_struct_0(sK3))
    | k1_yellow_0(sK3,X0_69) = X0_67 ),
    inference(subtyping,[status(esa)],[c_1155])).

cnf(c_2679,plain,
    ( k1_yellow_0(sK3,X0_69) = X0_67
    | r2_lattice3(sK3,X0_69,X0_67) != iProver_top
    | r2_lattice3(sK3,X0_69,sK0(sK3,X0_67,X0_69)) = iProver_top
    | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2223])).

cnf(c_4,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_37,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_682,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_37])).

cnf(c_683,plain,
    ( r1_orders_2(sK3,X0,X1)
    | ~ r3_orders_2(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_682])).

cnf(c_33,negated_conjecture,
    ( v2_lattice3(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_5,plain,
    ( ~ v2_lattice3(X0)
    | ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_108,plain,
    ( ~ v2_lattice3(sK3)
    | ~ v2_struct_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_687,plain,
    ( r1_orders_2(sK3,X0,X1)
    | ~ r3_orders_2(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_683,c_33,c_31,c_72,c_108])).

cnf(c_688,plain,
    ( r1_orders_2(sK3,X0,X1)
    | ~ r3_orders_2(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_687])).

cnf(c_23,negated_conjecture,
    ( r3_waybel_9(sK3,sK5,sK4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_27,negated_conjecture,
    ( v7_waybel_0(sK5) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_20,plain,
    ( ~ v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0)
    | ~ r3_waybel_9(X0,X1,X2)
    | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
    | r3_orders_2(X0,X2,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_25,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(sK3,X0),sK3,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_531,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
    | r3_orders_2(X0,X2,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(sK3))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X0)
    | k4_waybel_1(X0,sK2(X0)) != k4_waybel_1(sK3,X4)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_25])).

cnf(c_532,plain,
    ( ~ r3_waybel_9(sK3,X0,X1)
    | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
    | r3_orders_2(sK3,X1,X2)
    | ~ l1_waybel_0(X0,sK3)
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ v2_pre_topc(sK3)
    | ~ v8_pre_topc(sK3)
    | ~ v1_lattice3(sK3)
    | ~ v1_compts_1(sK3)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK3)
    | ~ v7_waybel_0(X0)
    | ~ l1_waybel_9(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v2_lattice3(sK3)
    | v2_struct_0(X0)
    | ~ v3_orders_2(sK3)
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X3) ),
    inference(unflattening,[status(thm)],[c_531])).

cnf(c_39,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_38,negated_conjecture,
    ( v8_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_36,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_34,negated_conjecture,
    ( v1_lattice3(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_32,negated_conjecture,
    ( v1_compts_1(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_536,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_532,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_31])).

cnf(c_537,plain,
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
    inference(renaming,[status(thm)],[c_536])).

cnf(c_770,plain,
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
    inference(resolution_lifted,[status(thm)],[c_27,c_537])).

cnf(c_771,plain,
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
    inference(unflattening,[status(thm)],[c_770])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_28,negated_conjecture,
    ( v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_26,negated_conjecture,
    ( l1_waybel_0(sK5,sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_775,plain,
    ( r3_orders_2(sK3,X0,X1)
    | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
    | ~ r3_waybel_9(sK3,sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_771,c_29,c_28,c_26])).

cnf(c_776,plain,
    ( ~ r3_waybel_9(sK3,sK5,X0)
    | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
    | r3_orders_2(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X2) ),
    inference(renaming,[status(thm)],[c_775])).

cnf(c_910,plain,
    ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | r3_orders_2(sK3,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X2)
    | sK4 != X1
    | sK5 != sK5
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_776])).

cnf(c_911,plain,
    ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | r3_orders_2(sK3,sK4,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1) ),
    inference(unflattening,[status(thm)],[c_910])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_915,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r3_orders_2(sK3,sK4,X0)
    | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_911,c_30])).

cnf(c_916,plain,
    ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | r3_orders_2(sK3,sK4,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1) ),
    inference(renaming,[status(thm)],[c_915])).

cnf(c_1039,plain,
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
    inference(resolution_lifted,[status(thm)],[c_688,c_916])).

cnf(c_1040,plain,
    ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | r1_orders_2(sK3,sK4,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1) ),
    inference(unflattening,[status(thm)],[c_1039])).

cnf(c_1044,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r1_orders_2(sK3,sK4,X0)
    | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1040,c_30])).

cnf(c_1045,plain,
    ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | r1_orders_2(sK3,sK4,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1) ),
    inference(renaming,[status(thm)],[c_1044])).

cnf(c_2227,plain,
    ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_67)
    | r1_orders_2(sK3,sK4,X0_67)
    | ~ m1_subset_1(X1_67,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_67,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1_67) ),
    inference(subtyping,[status(esa)],[c_1045])).

cnf(c_2239,plain,
    ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_67)
    | r1_orders_2(sK3,sK4,X0_67)
    | ~ m1_subset_1(X0_67,u1_struct_0(sK3))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_2227])).

cnf(c_2674,plain,
    ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_67) != iProver_top
    | r1_orders_2(sK3,sK4,X0_67) = iProver_top
    | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2239])).

cnf(c_21,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
    | r3_orders_2(X0,X2,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_607,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
    | r3_orders_2(X0,X2,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | m1_subset_1(sK2(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_lattice3(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_32])).

cnf(c_608,plain,
    ( ~ r3_waybel_9(sK3,X0,X1)
    | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
    | r3_orders_2(sK3,X1,X2)
    | ~ l1_waybel_0(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
    | ~ v2_pre_topc(sK3)
    | ~ v8_pre_topc(sK3)
    | ~ v1_lattice3(sK3)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK3)
    | ~ v7_waybel_0(X0)
    | ~ l1_waybel_9(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v2_lattice3(sK3)
    | v2_struct_0(X0)
    | ~ v3_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_607])).

cnf(c_612,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_608,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_31])).

cnf(c_613,plain,
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
    inference(renaming,[status(thm)],[c_612])).

cnf(c_740,plain,
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
    inference(resolution_lifted,[status(thm)],[c_27,c_613])).

cnf(c_741,plain,
    ( ~ r3_waybel_9(sK3,sK5,X0)
    | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
    | r3_orders_2(sK3,X0,X1)
    | ~ l1_waybel_0(sK5,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
    | ~ v4_orders_2(sK5)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_740])).

cnf(c_745,plain,
    ( r3_orders_2(sK3,X0,X1)
    | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
    | ~ r3_waybel_9(sK3,sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_741,c_29,c_28,c_26])).

cnf(c_746,plain,
    ( ~ r3_waybel_9(sK3,sK5,X0)
    | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
    | r3_orders_2(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_745])).

cnf(c_937,plain,
    ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | r3_orders_2(sK3,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
    | sK4 != X1
    | sK5 != sK5
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_746])).

cnf(c_938,plain,
    ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | r3_orders_2(sK3,sK4,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_937])).

cnf(c_942,plain,
    ( m1_subset_1(sK2(sK3),u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r3_orders_2(sK3,sK4,X0)
    | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_938,c_30])).

cnf(c_943,plain,
    ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | r3_orders_2(sK3,sK4,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_942])).

cnf(c_1015,plain,
    ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | r1_orders_2(sK3,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
    | X0 != X2
    | sK4 != X1
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_688,c_943])).

cnf(c_1016,plain,
    ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | r1_orders_2(sK3,sK4,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_1015])).

cnf(c_1020,plain,
    ( m1_subset_1(sK2(sK3),u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r1_orders_2(sK3,sK4,X0)
    | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1016,c_30])).

cnf(c_1021,plain,
    ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | r1_orders_2(sK3,sK4,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_1020])).

cnf(c_2228,plain,
    ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_67)
    | r1_orders_2(sK3,sK4,X0_67)
    | ~ m1_subset_1(X0_67,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1021])).

cnf(c_2306,plain,
    ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_67) != iProver_top
    | r1_orders_2(sK3,sK4,X0_67) = iProver_top
    | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2228])).

cnf(c_2240,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_2227])).

cnf(c_2309,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2240])).

cnf(c_2310,plain,
    ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_67) != iProver_top
    | r1_orders_2(sK3,sK4,X0_67) = iProver_top
    | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2239])).

cnf(c_2238,plain,
    ( ~ m1_subset_1(X0_67,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X0_67)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_2227])).

cnf(c_2675,plain,
    ( k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X0_67)
    | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2238])).

cnf(c_3464,plain,
    ( m1_subset_1(sK2(sK3),u1_struct_0(sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2675])).

cnf(c_3509,plain,
    ( m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top
    | r1_orders_2(sK3,sK4,X0_67) = iProver_top
    | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_67) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2674,c_2306,c_2309,c_2310,c_3464])).

cnf(c_3510,plain,
    ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_67) != iProver_top
    | r1_orders_2(sK3,sK4,X0_67) = iProver_top
    | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3509])).

cnf(c_14,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_432,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_orders_2(X2)
    | X2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_2])).

cnf(c_433,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(unflattening,[status(thm)],[c_432])).

cnf(c_818,plain,
    ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ l1_orders_2(X0)
    | sK5 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_433,c_26])).

cnf(c_819,plain,
    ( m1_subset_1(u1_waybel_0(sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_818])).

cnf(c_821,plain,
    ( m1_subset_1(u1_waybel_0(sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_819,c_31,c_72])).

cnf(c_2233,plain,
    ( m1_subset_1(u1_waybel_0(sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_821])).

cnf(c_2668,plain,
    ( m1_subset_1(u1_waybel_0(sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2233])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2236,plain,
    ( ~ m1_subset_1(X0_67,k1_zfmisc_1(k2_zfmisc_1(X0_70,X1_70)))
    | k2_relset_1(X0_70,X1_70,X0_67) = k2_relat_1(X0_67) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2666,plain,
    ( k2_relset_1(X0_70,X1_70,X0_67) = k2_relat_1(X0_67)
    | m1_subset_1(X0_67,k1_zfmisc_1(k2_zfmisc_1(X0_70,X1_70))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2236])).

cnf(c_2927,plain,
    ( k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)) = k2_relat_1(u1_waybel_0(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_2668,c_2666])).

cnf(c_3515,plain,
    ( r2_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_67) != iProver_top
    | r1_orders_2(sK3,sK4,X0_67) = iProver_top
    | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3510,c_2927])).

cnf(c_3523,plain,
    ( k1_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = X0_67
    | r2_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_67) != iProver_top
    | r1_orders_2(sK3,sK4,sK0(sK3,X0_67,k2_relat_1(u1_waybel_0(sK3,sK5)))) = iProver_top
    | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK0(sK3,X0_67,k2_relat_1(u1_waybel_0(sK3,sK5))),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2679,c_3515])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2237,plain,
    ( ~ m1_subset_1(X0_67,k1_zfmisc_1(k2_zfmisc_1(X0_70,X1_70)))
    | v1_relat_1(X0_67) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2665,plain,
    ( m1_subset_1(X0_67,k1_zfmisc_1(k2_zfmisc_1(X0_70,X1_70))) != iProver_top
    | v1_relat_1(X0_67) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2237])).

cnf(c_2922,plain,
    ( v1_relat_1(u1_waybel_0(sK3,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2668,c_2665])).

cnf(c_16,plain,
    ( v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_relat_1(X1)
    | k1_yellow_0(X0,k2_relat_1(X1)) = k4_yellow_2(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_669,plain,
    ( ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_33])).

cnf(c_670,plain,
    ( ~ v2_struct_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_669])).

cnf(c_672,plain,
    ( ~ v2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_670,c_33,c_31,c_72,c_108])).

cnf(c_855,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_relat_1(X1)
    | k1_yellow_0(X0,k2_relat_1(X1)) = k4_yellow_2(X0,X1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_672])).

cnf(c_856,plain,
    ( ~ l1_orders_2(sK3)
    | ~ v1_relat_1(X0)
    | k1_yellow_0(sK3,k2_relat_1(X0)) = k4_yellow_2(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_855])).

cnf(c_860,plain,
    ( ~ v1_relat_1(X0)
    | k1_yellow_0(sK3,k2_relat_1(X0)) = k4_yellow_2(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_856,c_31,c_72])).

cnf(c_2231,plain,
    ( ~ v1_relat_1(X0_67)
    | k1_yellow_0(sK3,k2_relat_1(X0_67)) = k4_yellow_2(sK3,X0_67) ),
    inference(subtyping,[status(esa)],[c_860])).

cnf(c_2669,plain,
    ( k1_yellow_0(sK3,k2_relat_1(X0_67)) = k4_yellow_2(sK3,X0_67)
    | v1_relat_1(X0_67) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2231])).

cnf(c_3190,plain,
    ( k1_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = k4_yellow_2(sK3,u1_waybel_0(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_2922,c_2669])).

cnf(c_15,plain,
    ( ~ l1_waybel_0(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | k4_yellow_2(X1,u1_waybel_0(X1,X0)) = k1_waybel_2(X1,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_829,plain,
    ( v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k4_yellow_2(X0,u1_waybel_0(X0,X1)) = k1_waybel_2(X0,X1)
    | sK5 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_26])).

cnf(c_830,plain,
    ( v2_struct_0(sK3)
    | ~ l1_orders_2(sK3)
    | k4_yellow_2(sK3,u1_waybel_0(sK3,sK5)) = k1_waybel_2(sK3,sK5) ),
    inference(unflattening,[status(thm)],[c_829])).

cnf(c_832,plain,
    ( k4_yellow_2(sK3,u1_waybel_0(sK3,sK5)) = k1_waybel_2(sK3,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_830,c_33,c_31,c_72,c_108])).

cnf(c_2232,plain,
    ( k4_yellow_2(sK3,u1_waybel_0(sK3,sK5)) = k1_waybel_2(sK3,sK5) ),
    inference(subtyping,[status(esa)],[c_832])).

cnf(c_3191,plain,
    ( k1_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = k1_waybel_2(sK3,sK5) ),
    inference(light_normalisation,[status(thm)],[c_3190,c_2232])).

cnf(c_3541,plain,
    ( k1_waybel_2(sK3,sK5) = X0_67
    | r2_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_67) != iProver_top
    | r1_orders_2(sK3,sK4,sK0(sK3,X0_67,k2_relat_1(u1_waybel_0(sK3,sK5)))) = iProver_top
    | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK0(sK3,X0_67,k2_relat_1(u1_waybel_0(sK3,sK5))),u1_struct_0(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3523,c_3191])).

cnf(c_3791,plain,
    ( k1_waybel_2(sK3,sK5) = X0_67
    | k1_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = X0_67
    | r2_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_67) != iProver_top
    | r1_orders_2(sK3,sK4,sK0(sK3,X0_67,k2_relat_1(u1_waybel_0(sK3,sK5)))) = iProver_top
    | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2678,c_3541])).

cnf(c_3797,plain,
    ( k1_waybel_2(sK3,sK5) = X0_67
    | r2_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_67) != iProver_top
    | r1_orders_2(sK3,sK4,sK0(sK3,X0_67,k2_relat_1(u1_waybel_0(sK3,sK5)))) = iProver_top
    | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3791,c_3191])).

cnf(c_9,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1173,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_35])).

cnf(c_1174,plain,
    ( ~ r2_lattice3(sK3,X0,X1)
    | ~ r1_orders_2(sK3,X1,sK0(sK3,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | k1_yellow_0(sK3,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1173])).

cnf(c_1178,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r1_orders_2(sK3,X1,sK0(sK3,X1,X0))
    | ~ r2_lattice3(sK3,X0,X1)
    | k1_yellow_0(sK3,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1174,c_31,c_72])).

cnf(c_1179,plain,
    ( ~ r2_lattice3(sK3,X0,X1)
    | ~ r1_orders_2(sK3,X1,sK0(sK3,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k1_yellow_0(sK3,X0) = X1 ),
    inference(renaming,[status(thm)],[c_1178])).

cnf(c_2222,plain,
    ( ~ r2_lattice3(sK3,X0_69,X0_67)
    | ~ r1_orders_2(sK3,X0_67,sK0(sK3,X0_67,X0_69))
    | ~ m1_subset_1(X0_67,u1_struct_0(sK3))
    | k1_yellow_0(sK3,X0_69) = X0_67 ),
    inference(subtyping,[status(esa)],[c_1179])).

cnf(c_2680,plain,
    ( k1_yellow_0(sK3,X0_69) = X0_67
    | r2_lattice3(sK3,X0_69,X0_67) != iProver_top
    | r1_orders_2(sK3,X0_67,sK0(sK3,X0_67,X0_69)) != iProver_top
    | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2222])).

cnf(c_3811,plain,
    ( k1_waybel_2(sK3,sK5) = sK4
    | k1_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = sK4
    | r2_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),sK4) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3797,c_2680])).

cnf(c_3816,plain,
    ( k1_waybel_2(sK3,sK5) = sK4
    | r2_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),sK4) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3811,c_3191])).

cnf(c_18,plain,
    ( ~ v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0)
    | ~ r3_waybel_9(X0,X1,X2)
    | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
    | ~ v10_waybel_0(X1,X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_24,negated_conjecture,
    ( v10_waybel_0(sK5,sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_497,plain,
    ( ~ v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0)
    | ~ r3_waybel_9(X0,X1,X2)
    | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X0)
    | sK5 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_24])).

cnf(c_498,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK3,sK1(sK3)),sK3,sK3)
    | ~ r3_waybel_9(sK3,sK5,X0)
    | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | ~ l1_waybel_0(sK5,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ v2_pre_topc(sK3)
    | ~ v8_pre_topc(sK3)
    | ~ v1_lattice3(sK3)
    | ~ v1_compts_1(sK3)
    | ~ v4_orders_2(sK5)
    | ~ v4_orders_2(sK3)
    | ~ v7_waybel_0(sK5)
    | ~ l1_waybel_9(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v2_lattice3(sK3)
    | v2_struct_0(sK5)
    | ~ v3_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_497])).

cnf(c_502,plain,
    ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | ~ r3_waybel_9(sK3,sK5,X0)
    | ~ v5_pre_topc(k4_waybel_1(sK3,sK1(sK3)),sK3,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_498,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_31,c_29,c_28,c_27,c_26])).

cnf(c_503,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK3,sK1(sK3)),sK3,sK3)
    | ~ r3_waybel_9(sK3,sK5,X0)
    | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_502])).

cnf(c_576,plain,
    ( ~ r3_waybel_9(sK3,sK5,X0)
    | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X1)
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_503])).

cnf(c_961,plain,
    ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X1)
    | sK4 != X0
    | sK5 != sK5
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_576])).

cnf(c_962,plain,
    ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_961])).

cnf(c_966,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
    | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_962,c_30])).

cnf(c_967,plain,
    ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0) ),
    inference(renaming,[status(thm)],[c_966])).

cnf(c_2230,plain,
    ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
    | ~ m1_subset_1(X0_67,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0_67) ),
    inference(subtyping,[status(esa)],[c_967])).

cnf(c_2670,plain,
    ( k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0_67)
    | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) = iProver_top
    | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2230])).

cnf(c_19,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
    | ~ v10_waybel_0(X1,X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_473,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X0)
    | sK5 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_24])).

cnf(c_474,plain,
    ( ~ r3_waybel_9(sK3,sK5,X0)
    | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | ~ l1_waybel_0(sK5,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3),u1_struct_0(sK3))
    | ~ v2_pre_topc(sK3)
    | ~ v8_pre_topc(sK3)
    | ~ v1_lattice3(sK3)
    | ~ v1_compts_1(sK3)
    | ~ v4_orders_2(sK5)
    | ~ v4_orders_2(sK3)
    | ~ v7_waybel_0(sK5)
    | ~ l1_waybel_9(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v2_lattice3(sK3)
    | v2_struct_0(sK5)
    | ~ v3_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_473])).

cnf(c_478,plain,
    ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | ~ r3_waybel_9(sK3,sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_474,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_31,c_29,c_28,c_27,c_26])).

cnf(c_479,plain,
    ( ~ r3_waybel_9(sK3,sK5,X0)
    | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_478])).

cnf(c_982,plain,
    ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3),u1_struct_0(sK3))
    | sK4 != X0
    | sK5 != sK5
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_479])).

cnf(c_983,plain,
    ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
    | m1_subset_1(sK1(sK3),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_982])).

cnf(c_985,plain,
    ( m1_subset_1(sK1(sK3),u1_struct_0(sK3))
    | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_983,c_30])).

cnf(c_986,plain,
    ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
    | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_985])).

cnf(c_987,plain,
    ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) = iProver_top
    | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_986])).

cnf(c_2246,plain,
    ( X0_71 = X0_71 ),
    theory(equality)).

cnf(c_2861,plain,
    ( k4_waybel_1(sK3,sK1(sK3)) = k4_waybel_1(sK3,sK1(sK3)) ),
    inference(instantiation,[status(thm)],[c_2246])).

cnf(c_2862,plain,
    ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
    | ~ m1_subset_1(sK1(sK3),u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,sK1(sK3)) ),
    inference(instantiation,[status(thm)],[c_2230])).

cnf(c_2863,plain,
    ( k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,sK1(sK3))
    | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) = iProver_top
    | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2862])).

cnf(c_2873,plain,
    ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2670,c_987,c_2861,c_2863])).

cnf(c_2979,plain,
    ( r2_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2927,c_2873])).

cnf(c_22,negated_conjecture,
    ( k1_waybel_2(sK3,sK5) != sK4 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2235,negated_conjecture,
    ( k1_waybel_2(sK3,sK5) != sK4 ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_49,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3816,c_2979,c_2235,c_49])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:04:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.16/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.00  
% 2.16/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.16/1.00  
% 2.16/1.00  ------  iProver source info
% 2.16/1.00  
% 2.16/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.16/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.16/1.00  git: non_committed_changes: false
% 2.16/1.00  git: last_make_outside_of_git: false
% 2.16/1.00  
% 2.16/1.00  ------ 
% 2.16/1.00  
% 2.16/1.00  ------ Input Options
% 2.16/1.00  
% 2.16/1.00  --out_options                           all
% 2.16/1.00  --tptp_safe_out                         true
% 2.16/1.00  --problem_path                          ""
% 2.16/1.00  --include_path                          ""
% 2.16/1.00  --clausifier                            res/vclausify_rel
% 2.16/1.00  --clausifier_options                    --mode clausify
% 2.16/1.00  --stdin                                 false
% 2.16/1.00  --stats_out                             all
% 2.16/1.00  
% 2.16/1.00  ------ General Options
% 2.16/1.00  
% 2.16/1.00  --fof                                   false
% 2.16/1.00  --time_out_real                         305.
% 2.16/1.00  --time_out_virtual                      -1.
% 2.16/1.00  --symbol_type_check                     false
% 2.16/1.00  --clausify_out                          false
% 2.16/1.00  --sig_cnt_out                           false
% 2.16/1.00  --trig_cnt_out                          false
% 2.16/1.00  --trig_cnt_out_tolerance                1.
% 2.16/1.00  --trig_cnt_out_sk_spl                   false
% 2.16/1.00  --abstr_cl_out                          false
% 2.16/1.00  
% 2.16/1.00  ------ Global Options
% 2.16/1.00  
% 2.16/1.00  --schedule                              default
% 2.16/1.00  --add_important_lit                     false
% 2.16/1.00  --prop_solver_per_cl                    1000
% 2.16/1.00  --min_unsat_core                        false
% 2.16/1.00  --soft_assumptions                      false
% 2.16/1.00  --soft_lemma_size                       3
% 2.16/1.00  --prop_impl_unit_size                   0
% 2.16/1.00  --prop_impl_unit                        []
% 2.16/1.00  --share_sel_clauses                     true
% 2.16/1.00  --reset_solvers                         false
% 2.16/1.00  --bc_imp_inh                            [conj_cone]
% 2.16/1.00  --conj_cone_tolerance                   3.
% 2.16/1.00  --extra_neg_conj                        none
% 2.16/1.00  --large_theory_mode                     true
% 2.16/1.00  --prolific_symb_bound                   200
% 2.16/1.00  --lt_threshold                          2000
% 2.16/1.00  --clause_weak_htbl                      true
% 2.16/1.00  --gc_record_bc_elim                     false
% 2.16/1.00  
% 2.16/1.00  ------ Preprocessing Options
% 2.16/1.00  
% 2.16/1.00  --preprocessing_flag                    true
% 2.16/1.00  --time_out_prep_mult                    0.1
% 2.16/1.00  --splitting_mode                        input
% 2.16/1.00  --splitting_grd                         true
% 2.16/1.00  --splitting_cvd                         false
% 2.16/1.00  --splitting_cvd_svl                     false
% 2.16/1.00  --splitting_nvd                         32
% 2.16/1.00  --sub_typing                            true
% 2.16/1.00  --prep_gs_sim                           true
% 2.16/1.00  --prep_unflatten                        true
% 2.16/1.00  --prep_res_sim                          true
% 2.16/1.00  --prep_upred                            true
% 2.16/1.00  --prep_sem_filter                       exhaustive
% 2.16/1.00  --prep_sem_filter_out                   false
% 2.16/1.00  --pred_elim                             true
% 2.16/1.00  --res_sim_input                         true
% 2.16/1.00  --eq_ax_congr_red                       true
% 2.16/1.00  --pure_diseq_elim                       true
% 2.16/1.00  --brand_transform                       false
% 2.16/1.00  --non_eq_to_eq                          false
% 2.16/1.00  --prep_def_merge                        true
% 2.16/1.00  --prep_def_merge_prop_impl              false
% 2.16/1.00  --prep_def_merge_mbd                    true
% 2.16/1.00  --prep_def_merge_tr_red                 false
% 2.16/1.00  --prep_def_merge_tr_cl                  false
% 2.16/1.00  --smt_preprocessing                     true
% 2.16/1.00  --smt_ac_axioms                         fast
% 2.16/1.00  --preprocessed_out                      false
% 2.16/1.00  --preprocessed_stats                    false
% 2.16/1.00  
% 2.16/1.00  ------ Abstraction refinement Options
% 2.16/1.00  
% 2.16/1.00  --abstr_ref                             []
% 2.16/1.00  --abstr_ref_prep                        false
% 2.16/1.00  --abstr_ref_until_sat                   false
% 2.16/1.00  --abstr_ref_sig_restrict                funpre
% 2.16/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.16/1.00  --abstr_ref_under                       []
% 2.16/1.00  
% 2.16/1.00  ------ SAT Options
% 2.16/1.00  
% 2.16/1.00  --sat_mode                              false
% 2.16/1.00  --sat_fm_restart_options                ""
% 2.16/1.00  --sat_gr_def                            false
% 2.16/1.00  --sat_epr_types                         true
% 2.16/1.00  --sat_non_cyclic_types                  false
% 2.16/1.00  --sat_finite_models                     false
% 2.16/1.00  --sat_fm_lemmas                         false
% 2.16/1.00  --sat_fm_prep                           false
% 2.16/1.00  --sat_fm_uc_incr                        true
% 2.16/1.00  --sat_out_model                         small
% 2.16/1.00  --sat_out_clauses                       false
% 2.16/1.00  
% 2.16/1.00  ------ QBF Options
% 2.16/1.00  
% 2.16/1.00  --qbf_mode                              false
% 2.16/1.00  --qbf_elim_univ                         false
% 2.16/1.00  --qbf_dom_inst                          none
% 2.16/1.00  --qbf_dom_pre_inst                      false
% 2.16/1.00  --qbf_sk_in                             false
% 2.16/1.00  --qbf_pred_elim                         true
% 2.16/1.00  --qbf_split                             512
% 2.16/1.00  
% 2.16/1.00  ------ BMC1 Options
% 2.16/1.00  
% 2.16/1.00  --bmc1_incremental                      false
% 2.16/1.00  --bmc1_axioms                           reachable_all
% 2.16/1.00  --bmc1_min_bound                        0
% 2.16/1.00  --bmc1_max_bound                        -1
% 2.16/1.00  --bmc1_max_bound_default                -1
% 2.16/1.00  --bmc1_symbol_reachability              true
% 2.16/1.00  --bmc1_property_lemmas                  false
% 2.16/1.00  --bmc1_k_induction                      false
% 2.16/1.00  --bmc1_non_equiv_states                 false
% 2.16/1.00  --bmc1_deadlock                         false
% 2.16/1.00  --bmc1_ucm                              false
% 2.16/1.00  --bmc1_add_unsat_core                   none
% 2.16/1.00  --bmc1_unsat_core_children              false
% 2.16/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.16/1.00  --bmc1_out_stat                         full
% 2.16/1.00  --bmc1_ground_init                      false
% 2.16/1.00  --bmc1_pre_inst_next_state              false
% 2.16/1.00  --bmc1_pre_inst_state                   false
% 2.16/1.00  --bmc1_pre_inst_reach_state             false
% 2.16/1.00  --bmc1_out_unsat_core                   false
% 2.16/1.00  --bmc1_aig_witness_out                  false
% 2.16/1.00  --bmc1_verbose                          false
% 2.16/1.00  --bmc1_dump_clauses_tptp                false
% 2.16/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.16/1.00  --bmc1_dump_file                        -
% 2.16/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.16/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.16/1.00  --bmc1_ucm_extend_mode                  1
% 2.16/1.00  --bmc1_ucm_init_mode                    2
% 2.16/1.00  --bmc1_ucm_cone_mode                    none
% 2.16/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.16/1.00  --bmc1_ucm_relax_model                  4
% 2.16/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.16/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.16/1.00  --bmc1_ucm_layered_model                none
% 2.16/1.00  --bmc1_ucm_max_lemma_size               10
% 2.16/1.00  
% 2.16/1.00  ------ AIG Options
% 2.16/1.00  
% 2.16/1.00  --aig_mode                              false
% 2.16/1.00  
% 2.16/1.00  ------ Instantiation Options
% 2.16/1.00  
% 2.16/1.00  --instantiation_flag                    true
% 2.16/1.00  --inst_sos_flag                         false
% 2.16/1.00  --inst_sos_phase                        true
% 2.16/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.16/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.16/1.00  --inst_lit_sel_side                     num_symb
% 2.16/1.00  --inst_solver_per_active                1400
% 2.16/1.00  --inst_solver_calls_frac                1.
% 2.16/1.00  --inst_passive_queue_type               priority_queues
% 2.16/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.16/1.00  --inst_passive_queues_freq              [25;2]
% 2.16/1.00  --inst_dismatching                      true
% 2.16/1.00  --inst_eager_unprocessed_to_passive     true
% 2.16/1.00  --inst_prop_sim_given                   true
% 2.16/1.00  --inst_prop_sim_new                     false
% 2.16/1.00  --inst_subs_new                         false
% 2.16/1.00  --inst_eq_res_simp                      false
% 2.16/1.00  --inst_subs_given                       false
% 2.16/1.00  --inst_orphan_elimination               true
% 2.16/1.00  --inst_learning_loop_flag               true
% 2.16/1.00  --inst_learning_start                   3000
% 2.16/1.00  --inst_learning_factor                  2
% 2.16/1.00  --inst_start_prop_sim_after_learn       3
% 2.16/1.00  --inst_sel_renew                        solver
% 2.16/1.00  --inst_lit_activity_flag                true
% 2.16/1.00  --inst_restr_to_given                   false
% 2.16/1.00  --inst_activity_threshold               500
% 2.16/1.00  --inst_out_proof                        true
% 2.16/1.00  
% 2.16/1.00  ------ Resolution Options
% 2.16/1.00  
% 2.16/1.00  --resolution_flag                       true
% 2.16/1.00  --res_lit_sel                           adaptive
% 2.16/1.00  --res_lit_sel_side                      none
% 2.16/1.00  --res_ordering                          kbo
% 2.16/1.00  --res_to_prop_solver                    active
% 2.16/1.00  --res_prop_simpl_new                    false
% 2.16/1.00  --res_prop_simpl_given                  true
% 2.16/1.00  --res_passive_queue_type                priority_queues
% 2.16/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.16/1.00  --res_passive_queues_freq               [15;5]
% 2.16/1.00  --res_forward_subs                      full
% 2.16/1.00  --res_backward_subs                     full
% 2.16/1.00  --res_forward_subs_resolution           true
% 2.16/1.00  --res_backward_subs_resolution          true
% 2.16/1.00  --res_orphan_elimination                true
% 2.16/1.00  --res_time_limit                        2.
% 2.16/1.00  --res_out_proof                         true
% 2.16/1.00  
% 2.16/1.00  ------ Superposition Options
% 2.16/1.00  
% 2.16/1.00  --superposition_flag                    true
% 2.16/1.00  --sup_passive_queue_type                priority_queues
% 2.16/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.16/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.16/1.00  --demod_completeness_check              fast
% 2.16/1.00  --demod_use_ground                      true
% 2.16/1.00  --sup_to_prop_solver                    passive
% 2.16/1.00  --sup_prop_simpl_new                    true
% 2.16/1.00  --sup_prop_simpl_given                  true
% 2.16/1.00  --sup_fun_splitting                     false
% 2.16/1.00  --sup_smt_interval                      50000
% 2.16/1.00  
% 2.16/1.00  ------ Superposition Simplification Setup
% 2.16/1.00  
% 2.16/1.00  --sup_indices_passive                   []
% 2.16/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.16/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.00  --sup_full_bw                           [BwDemod]
% 2.16/1.00  --sup_immed_triv                        [TrivRules]
% 2.16/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.16/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.00  --sup_immed_bw_main                     []
% 2.16/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.16/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.00  
% 2.16/1.00  ------ Combination Options
% 2.16/1.00  
% 2.16/1.00  --comb_res_mult                         3
% 2.16/1.00  --comb_sup_mult                         2
% 2.16/1.00  --comb_inst_mult                        10
% 2.16/1.00  
% 2.16/1.00  ------ Debug Options
% 2.16/1.00  
% 2.16/1.00  --dbg_backtrace                         false
% 2.16/1.00  --dbg_dump_prop_clauses                 false
% 2.16/1.00  --dbg_dump_prop_clauses_file            -
% 2.16/1.00  --dbg_out_stat                          false
% 2.16/1.00  ------ Parsing...
% 2.16/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.16/1.00  
% 2.16/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe:16:0s pe_e  sf_s  rm: 16 0s  sf_e  pe_s  pe_e 
% 2.16/1.00  
% 2.16/1.00  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.16/1.00  
% 2.16/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.16/1.00  ------ Proving...
% 2.16/1.00  ------ Problem Properties 
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  clauses                                 22
% 2.16/1.00  conjectures                             2
% 2.16/1.00  EPR                                     1
% 2.16/1.00  Horn                                    15
% 2.16/1.00  unary                                   4
% 2.16/1.00  binary                                  5
% 2.16/1.00  lits                                    63
% 2.16/1.00  lits eq                                 11
% 2.16/1.00  fd_pure                                 0
% 2.16/1.00  fd_pseudo                               0
% 2.16/1.00  fd_cond                                 0
% 2.16/1.00  fd_pseudo_cond                          3
% 2.16/1.00  AC symbols                              0
% 2.16/1.00  
% 2.16/1.00  ------ Schedule dynamic 5 is on 
% 2.16/1.00  
% 2.16/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  ------ 
% 2.16/1.00  Current options:
% 2.16/1.00  ------ 
% 2.16/1.00  
% 2.16/1.00  ------ Input Options
% 2.16/1.00  
% 2.16/1.00  --out_options                           all
% 2.16/1.00  --tptp_safe_out                         true
% 2.16/1.00  --problem_path                          ""
% 2.16/1.00  --include_path                          ""
% 2.16/1.00  --clausifier                            res/vclausify_rel
% 2.16/1.00  --clausifier_options                    --mode clausify
% 2.16/1.00  --stdin                                 false
% 2.16/1.00  --stats_out                             all
% 2.16/1.00  
% 2.16/1.00  ------ General Options
% 2.16/1.00  
% 2.16/1.00  --fof                                   false
% 2.16/1.00  --time_out_real                         305.
% 2.16/1.00  --time_out_virtual                      -1.
% 2.16/1.00  --symbol_type_check                     false
% 2.16/1.00  --clausify_out                          false
% 2.16/1.00  --sig_cnt_out                           false
% 2.16/1.00  --trig_cnt_out                          false
% 2.16/1.00  --trig_cnt_out_tolerance                1.
% 2.16/1.00  --trig_cnt_out_sk_spl                   false
% 2.16/1.00  --abstr_cl_out                          false
% 2.16/1.00  
% 2.16/1.00  ------ Global Options
% 2.16/1.00  
% 2.16/1.00  --schedule                              default
% 2.16/1.00  --add_important_lit                     false
% 2.16/1.00  --prop_solver_per_cl                    1000
% 2.16/1.00  --min_unsat_core                        false
% 2.16/1.00  --soft_assumptions                      false
% 2.16/1.00  --soft_lemma_size                       3
% 2.16/1.00  --prop_impl_unit_size                   0
% 2.16/1.00  --prop_impl_unit                        []
% 2.16/1.00  --share_sel_clauses                     true
% 2.16/1.00  --reset_solvers                         false
% 2.16/1.00  --bc_imp_inh                            [conj_cone]
% 2.16/1.00  --conj_cone_tolerance                   3.
% 2.16/1.00  --extra_neg_conj                        none
% 2.16/1.00  --large_theory_mode                     true
% 2.16/1.00  --prolific_symb_bound                   200
% 2.16/1.00  --lt_threshold                          2000
% 2.16/1.00  --clause_weak_htbl                      true
% 2.16/1.00  --gc_record_bc_elim                     false
% 2.16/1.00  
% 2.16/1.00  ------ Preprocessing Options
% 2.16/1.00  
% 2.16/1.00  --preprocessing_flag                    true
% 2.16/1.00  --time_out_prep_mult                    0.1
% 2.16/1.00  --splitting_mode                        input
% 2.16/1.00  --splitting_grd                         true
% 2.16/1.00  --splitting_cvd                         false
% 2.16/1.00  --splitting_cvd_svl                     false
% 2.16/1.00  --splitting_nvd                         32
% 2.16/1.00  --sub_typing                            true
% 2.16/1.00  --prep_gs_sim                           true
% 2.16/1.00  --prep_unflatten                        true
% 2.16/1.00  --prep_res_sim                          true
% 2.16/1.00  --prep_upred                            true
% 2.16/1.00  --prep_sem_filter                       exhaustive
% 2.16/1.00  --prep_sem_filter_out                   false
% 2.16/1.00  --pred_elim                             true
% 2.16/1.00  --res_sim_input                         true
% 2.16/1.00  --eq_ax_congr_red                       true
% 2.16/1.00  --pure_diseq_elim                       true
% 2.16/1.00  --brand_transform                       false
% 2.16/1.00  --non_eq_to_eq                          false
% 2.16/1.00  --prep_def_merge                        true
% 2.16/1.00  --prep_def_merge_prop_impl              false
% 2.16/1.00  --prep_def_merge_mbd                    true
% 2.16/1.00  --prep_def_merge_tr_red                 false
% 2.16/1.00  --prep_def_merge_tr_cl                  false
% 2.16/1.00  --smt_preprocessing                     true
% 2.16/1.00  --smt_ac_axioms                         fast
% 2.16/1.00  --preprocessed_out                      false
% 2.16/1.00  --preprocessed_stats                    false
% 2.16/1.00  
% 2.16/1.00  ------ Abstraction refinement Options
% 2.16/1.00  
% 2.16/1.00  --abstr_ref                             []
% 2.16/1.00  --abstr_ref_prep                        false
% 2.16/1.00  --abstr_ref_until_sat                   false
% 2.16/1.00  --abstr_ref_sig_restrict                funpre
% 2.16/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.16/1.00  --abstr_ref_under                       []
% 2.16/1.00  
% 2.16/1.00  ------ SAT Options
% 2.16/1.00  
% 2.16/1.00  --sat_mode                              false
% 2.16/1.00  --sat_fm_restart_options                ""
% 2.16/1.00  --sat_gr_def                            false
% 2.16/1.00  --sat_epr_types                         true
% 2.16/1.00  --sat_non_cyclic_types                  false
% 2.16/1.00  --sat_finite_models                     false
% 2.16/1.00  --sat_fm_lemmas                         false
% 2.16/1.00  --sat_fm_prep                           false
% 2.16/1.00  --sat_fm_uc_incr                        true
% 2.16/1.00  --sat_out_model                         small
% 2.16/1.00  --sat_out_clauses                       false
% 2.16/1.00  
% 2.16/1.00  ------ QBF Options
% 2.16/1.00  
% 2.16/1.00  --qbf_mode                              false
% 2.16/1.00  --qbf_elim_univ                         false
% 2.16/1.00  --qbf_dom_inst                          none
% 2.16/1.00  --qbf_dom_pre_inst                      false
% 2.16/1.00  --qbf_sk_in                             false
% 2.16/1.00  --qbf_pred_elim                         true
% 2.16/1.00  --qbf_split                             512
% 2.16/1.00  
% 2.16/1.00  ------ BMC1 Options
% 2.16/1.00  
% 2.16/1.00  --bmc1_incremental                      false
% 2.16/1.00  --bmc1_axioms                           reachable_all
% 2.16/1.00  --bmc1_min_bound                        0
% 2.16/1.00  --bmc1_max_bound                        -1
% 2.16/1.00  --bmc1_max_bound_default                -1
% 2.16/1.00  --bmc1_symbol_reachability              true
% 2.16/1.00  --bmc1_property_lemmas                  false
% 2.16/1.00  --bmc1_k_induction                      false
% 2.16/1.00  --bmc1_non_equiv_states                 false
% 2.16/1.00  --bmc1_deadlock                         false
% 2.16/1.00  --bmc1_ucm                              false
% 2.16/1.00  --bmc1_add_unsat_core                   none
% 2.16/1.00  --bmc1_unsat_core_children              false
% 2.16/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.16/1.00  --bmc1_out_stat                         full
% 2.16/1.00  --bmc1_ground_init                      false
% 2.16/1.00  --bmc1_pre_inst_next_state              false
% 2.16/1.00  --bmc1_pre_inst_state                   false
% 2.16/1.00  --bmc1_pre_inst_reach_state             false
% 2.16/1.00  --bmc1_out_unsat_core                   false
% 2.16/1.00  --bmc1_aig_witness_out                  false
% 2.16/1.00  --bmc1_verbose                          false
% 2.16/1.00  --bmc1_dump_clauses_tptp                false
% 2.16/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.16/1.00  --bmc1_dump_file                        -
% 2.16/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.16/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.16/1.00  --bmc1_ucm_extend_mode                  1
% 2.16/1.00  --bmc1_ucm_init_mode                    2
% 2.16/1.00  --bmc1_ucm_cone_mode                    none
% 2.16/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.16/1.00  --bmc1_ucm_relax_model                  4
% 2.16/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.16/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.16/1.00  --bmc1_ucm_layered_model                none
% 2.16/1.00  --bmc1_ucm_max_lemma_size               10
% 2.16/1.00  
% 2.16/1.00  ------ AIG Options
% 2.16/1.00  
% 2.16/1.00  --aig_mode                              false
% 2.16/1.00  
% 2.16/1.00  ------ Instantiation Options
% 2.16/1.00  
% 2.16/1.00  --instantiation_flag                    true
% 2.16/1.00  --inst_sos_flag                         false
% 2.16/1.00  --inst_sos_phase                        true
% 2.16/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.16/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.16/1.00  --inst_lit_sel_side                     none
% 2.16/1.00  --inst_solver_per_active                1400
% 2.16/1.00  --inst_solver_calls_frac                1.
% 2.16/1.00  --inst_passive_queue_type               priority_queues
% 2.16/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.16/1.00  --inst_passive_queues_freq              [25;2]
% 2.16/1.00  --inst_dismatching                      true
% 2.16/1.00  --inst_eager_unprocessed_to_passive     true
% 2.16/1.00  --inst_prop_sim_given                   true
% 2.16/1.00  --inst_prop_sim_new                     false
% 2.16/1.00  --inst_subs_new                         false
% 2.16/1.00  --inst_eq_res_simp                      false
% 2.16/1.00  --inst_subs_given                       false
% 2.16/1.00  --inst_orphan_elimination               true
% 2.16/1.00  --inst_learning_loop_flag               true
% 2.16/1.00  --inst_learning_start                   3000
% 2.16/1.00  --inst_learning_factor                  2
% 2.16/1.00  --inst_start_prop_sim_after_learn       3
% 2.16/1.00  --inst_sel_renew                        solver
% 2.16/1.00  --inst_lit_activity_flag                true
% 2.16/1.00  --inst_restr_to_given                   false
% 2.16/1.00  --inst_activity_threshold               500
% 2.16/1.00  --inst_out_proof                        true
% 2.16/1.00  
% 2.16/1.00  ------ Resolution Options
% 2.16/1.00  
% 2.16/1.00  --resolution_flag                       false
% 2.16/1.00  --res_lit_sel                           adaptive
% 2.16/1.00  --res_lit_sel_side                      none
% 2.16/1.00  --res_ordering                          kbo
% 2.16/1.00  --res_to_prop_solver                    active
% 2.16/1.00  --res_prop_simpl_new                    false
% 2.16/1.00  --res_prop_simpl_given                  true
% 2.16/1.00  --res_passive_queue_type                priority_queues
% 2.16/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.16/1.00  --res_passive_queues_freq               [15;5]
% 2.16/1.00  --res_forward_subs                      full
% 2.16/1.00  --res_backward_subs                     full
% 2.16/1.00  --res_forward_subs_resolution           true
% 2.16/1.00  --res_backward_subs_resolution          true
% 2.16/1.00  --res_orphan_elimination                true
% 2.16/1.00  --res_time_limit                        2.
% 2.16/1.00  --res_out_proof                         true
% 2.16/1.00  
% 2.16/1.00  ------ Superposition Options
% 2.16/1.00  
% 2.16/1.00  --superposition_flag                    true
% 2.16/1.00  --sup_passive_queue_type                priority_queues
% 2.16/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.16/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.16/1.00  --demod_completeness_check              fast
% 2.16/1.00  --demod_use_ground                      true
% 2.16/1.00  --sup_to_prop_solver                    passive
% 2.16/1.00  --sup_prop_simpl_new                    true
% 2.16/1.00  --sup_prop_simpl_given                  true
% 2.16/1.00  --sup_fun_splitting                     false
% 2.16/1.00  --sup_smt_interval                      50000
% 2.16/1.00  
% 2.16/1.00  ------ Superposition Simplification Setup
% 2.16/1.00  
% 2.16/1.00  --sup_indices_passive                   []
% 2.16/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.16/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.00  --sup_full_bw                           [BwDemod]
% 2.16/1.00  --sup_immed_triv                        [TrivRules]
% 2.16/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.16/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.00  --sup_immed_bw_main                     []
% 2.16/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.16/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.00  
% 2.16/1.00  ------ Combination Options
% 2.16/1.00  
% 2.16/1.00  --comb_res_mult                         3
% 2.16/1.00  --comb_sup_mult                         2
% 2.16/1.00  --comb_inst_mult                        10
% 2.16/1.00  
% 2.16/1.00  ------ Debug Options
% 2.16/1.00  
% 2.16/1.00  --dbg_backtrace                         false
% 2.16/1.00  --dbg_dump_prop_clauses                 false
% 2.16/1.00  --dbg_dump_prop_clauses_file            -
% 2.16/1.00  --dbg_out_stat                          false
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  ------ Proving...
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  % SZS status Theorem for theBenchmark.p
% 2.16/1.00  
% 2.16/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.16/1.00  
% 2.16/1.00  fof(f6,axiom,(
% 2.16/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1))))))),
% 2.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f15,plain,(
% 2.16/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X4) => r1_orders_2(X0,X1,X4))) & r2_lattice3(X0,X2,X1))))))),
% 2.16/1.00    inference(rectify,[],[f6])).
% 2.16/1.00  
% 2.16/1.00  fof(f27,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | (~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 2.16/1.00    inference(ennf_transformation,[],[f15])).
% 2.16/1.00  
% 2.16/1.00  fof(f28,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 2.16/1.00    inference(flattening,[],[f27])).
% 2.16/1.00  
% 2.16/1.00  fof(f43,plain,(
% 2.16/1.00    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X1,sK0(X0,X1,X2)) & r2_lattice3(X0,X2,sK0(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 2.16/1.00    introduced(choice_axiom,[])).
% 2.16/1.00  
% 2.16/1.00  fof(f44,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (~r1_orders_2(X0,X1,sK0(X0,X1,X2)) & r2_lattice3(X0,X2,sK0(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 2.16/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f43])).
% 2.16/1.00  
% 2.16/1.00  fof(f62,plain,(
% 2.16/1.00    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X2) = X1 | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f44])).
% 2.16/1.00  
% 2.16/1.00  fof(f13,conjecture,(
% 2.16/1.00    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => ((r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0))) => k1_waybel_2(X0,X2) = X1))))),
% 2.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f14,negated_conjecture,(
% 2.16/1.00    ~! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => ((r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0))) => k1_waybel_2(X0,X2) = X1))))),
% 2.16/1.00    inference(negated_conjecture,[],[f13])).
% 2.16/1.00  
% 2.16/1.00  fof(f40,plain,(
% 2.16/1.00    ? [X0] : (? [X1] : (? [X2] : ((k1_waybel_2(X0,X2) != X1 & (r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))))) & (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.16/1.00    inference(ennf_transformation,[],[f14])).
% 2.16/1.00  
% 2.16/1.00  fof(f41,plain,(
% 2.16/1.00    ? [X0] : (? [X1] : (? [X2] : (k1_waybel_2(X0,X2) != X1 & r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 2.16/1.00    inference(flattening,[],[f40])).
% 2.16/1.00  
% 2.16/1.00  fof(f52,plain,(
% 2.16/1.00    ( ! [X0,X1] : (? [X2] : (k1_waybel_2(X0,X2) != X1 & r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (k1_waybel_2(X0,sK5) != X1 & r3_waybel_9(X0,sK5,X1) & v10_waybel_0(sK5,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(sK5,X0) & v7_waybel_0(sK5) & v4_orders_2(sK5) & ~v2_struct_0(sK5))) )),
% 2.16/1.00    introduced(choice_axiom,[])).
% 2.16/1.00  
% 2.16/1.00  fof(f51,plain,(
% 2.16/1.00    ( ! [X0] : (? [X1] : (? [X2] : (k1_waybel_2(X0,X2) != X1 & r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_waybel_2(X0,X2) != sK4 & r3_waybel_9(X0,X2,sK4) & v10_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 2.16/1.00    introduced(choice_axiom,[])).
% 2.16/1.00  
% 2.16/1.00  fof(f50,plain,(
% 2.16/1.00    ? [X0] : (? [X1] : (? [X2] : (k1_waybel_2(X0,X2) != X1 & r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (k1_waybel_2(sK3,X2) != X1 & r3_waybel_9(sK3,X2,X1) & v10_waybel_0(X2,sK3) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK3,X3),sK3,sK3) | ~m1_subset_1(X3,u1_struct_0(sK3))) & l1_waybel_0(X2,sK3) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_waybel_9(sK3) & v1_compts_1(sK3) & v2_lattice3(sK3) & v1_lattice3(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & v8_pre_topc(sK3) & v2_pre_topc(sK3))),
% 2.16/1.00    introduced(choice_axiom,[])).
% 2.16/1.00  
% 2.16/1.00  fof(f53,plain,(
% 2.16/1.00    ((k1_waybel_2(sK3,sK5) != sK4 & r3_waybel_9(sK3,sK5,sK4) & v10_waybel_0(sK5,sK3) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK3,X3),sK3,sK3) | ~m1_subset_1(X3,u1_struct_0(sK3))) & l1_waybel_0(sK5,sK3) & v7_waybel_0(sK5) & v4_orders_2(sK5) & ~v2_struct_0(sK5)) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_waybel_9(sK3) & v1_compts_1(sK3) & v2_lattice3(sK3) & v1_lattice3(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & v8_pre_topc(sK3) & v2_pre_topc(sK3)),
% 2.16/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f41,f52,f51,f50])).
% 2.16/1.00  
% 2.16/1.00  fof(f80,plain,(
% 2.16/1.00    v5_orders_2(sK3)),
% 2.16/1.00    inference(cnf_transformation,[],[f53])).
% 2.16/1.00  
% 2.16/1.00  fof(f84,plain,(
% 2.16/1.00    l1_waybel_9(sK3)),
% 2.16/1.00    inference(cnf_transformation,[],[f53])).
% 2.16/1.00  
% 2.16/1.00  fof(f10,axiom,(
% 2.16/1.00    ! [X0] : (l1_waybel_9(X0) => (l1_orders_2(X0) & l1_pre_topc(X0)))),
% 2.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f17,plain,(
% 2.16/1.00    ! [X0] : (l1_waybel_9(X0) => l1_orders_2(X0))),
% 2.16/1.00    inference(pure_predicate_removal,[],[f10])).
% 2.16/1.00  
% 2.16/1.00  fof(f35,plain,(
% 2.16/1.00    ! [X0] : (l1_orders_2(X0) | ~l1_waybel_9(X0))),
% 2.16/1.00    inference(ennf_transformation,[],[f17])).
% 2.16/1.00  
% 2.16/1.00  fof(f71,plain,(
% 2.16/1.00    ( ! [X0] : (l1_orders_2(X0) | ~l1_waybel_9(X0)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f35])).
% 2.16/1.00  
% 2.16/1.00  fof(f63,plain,(
% 2.16/1.00    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X2) = X1 | r2_lattice3(X0,X2,sK0(X0,X1,X2)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f44])).
% 2.16/1.00  
% 2.16/1.00  fof(f4,axiom,(
% 2.16/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 2.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f23,plain,(
% 2.16/1.00    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.16/1.00    inference(ennf_transformation,[],[f4])).
% 2.16/1.00  
% 2.16/1.00  fof(f24,plain,(
% 2.16/1.00    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.16/1.00    inference(flattening,[],[f23])).
% 2.16/1.00  
% 2.16/1.00  fof(f42,plain,(
% 2.16/1.00    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.16/1.00    inference(nnf_transformation,[],[f24])).
% 2.16/1.00  
% 2.16/1.00  fof(f57,plain,(
% 2.16/1.00    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f42])).
% 2.16/1.00  
% 2.16/1.00  fof(f78,plain,(
% 2.16/1.00    v3_orders_2(sK3)),
% 2.16/1.00    inference(cnf_transformation,[],[f53])).
% 2.16/1.00  
% 2.16/1.00  fof(f82,plain,(
% 2.16/1.00    v2_lattice3(sK3)),
% 2.16/1.00    inference(cnf_transformation,[],[f53])).
% 2.16/1.00  
% 2.16/1.00  fof(f5,axiom,(
% 2.16/1.00    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 2.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f25,plain,(
% 2.16/1.00    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 2.16/1.00    inference(ennf_transformation,[],[f5])).
% 2.16/1.00  
% 2.16/1.00  fof(f26,plain,(
% 2.16/1.00    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 2.16/1.00    inference(flattening,[],[f25])).
% 2.16/1.00  
% 2.16/1.00  fof(f59,plain,(
% 2.16/1.00    ( ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f26])).
% 2.16/1.00  
% 2.16/1.00  fof(f92,plain,(
% 2.16/1.00    r3_waybel_9(sK3,sK5,sK4)),
% 2.16/1.00    inference(cnf_transformation,[],[f53])).
% 2.16/1.00  
% 2.16/1.00  fof(f88,plain,(
% 2.16/1.00    v7_waybel_0(sK5)),
% 2.16/1.00    inference(cnf_transformation,[],[f53])).
% 2.16/1.00  
% 2.16/1.00  fof(f12,axiom,(
% 2.16/1.00    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) => r3_orders_2(X0,X3,X4))))))))),
% 2.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f16,plain,(
% 2.16/1.00    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) => r3_orders_2(X0,X3,X5))))))))),
% 2.16/1.00    inference(rectify,[],[f12])).
% 2.16/1.00  
% 2.16/1.00  fof(f38,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X5] : ((r3_orders_2(X0,X3,X5) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)) | ~m1_subset_1(X5,u1_struct_0(X0))) | (~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.16/1.00    inference(ennf_transformation,[],[f16])).
% 2.16/1.00  
% 2.16/1.00  fof(f39,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X5] : (r3_orders_2(X0,X3,X5) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.16/1.00    inference(flattening,[],[f38])).
% 2.16/1.00  
% 2.16/1.00  fof(f47,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | ? [X5] : (~v5_pre_topc(k4_waybel_1(X0,X5),X0,X0) & m1_subset_1(X5,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.16/1.00    inference(rectify,[],[f39])).
% 2.16/1.00  
% 2.16/1.00  fof(f48,plain,(
% 2.16/1.00    ! [X0] : (? [X5] : (~v5_pre_topc(k4_waybel_1(X0,X5),X0,X0) & m1_subset_1(X5,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0) & m1_subset_1(sK2(X0),u1_struct_0(X0))))),
% 2.16/1.00    introduced(choice_axiom,[])).
% 2.16/1.00  
% 2.16/1.00  fof(f49,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | (~v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0) & m1_subset_1(sK2(X0),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.16/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f47,f48])).
% 2.16/1.00  
% 2.16/1.00  fof(f75,plain,(
% 2.16/1.00    ( ! [X4,X2,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | ~v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f49])).
% 2.16/1.00  
% 2.16/1.00  fof(f98,plain,(
% 2.16/1.00    ( ! [X4,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | ~v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.16/1.00    inference(equality_resolution,[],[f75])).
% 2.16/1.00  
% 2.16/1.00  fof(f90,plain,(
% 2.16/1.00    ( ! [X3] : (v5_pre_topc(k4_waybel_1(sK3,X3),sK3,sK3) | ~m1_subset_1(X3,u1_struct_0(sK3))) )),
% 2.16/1.00    inference(cnf_transformation,[],[f53])).
% 2.16/1.00  
% 2.16/1.00  fof(f76,plain,(
% 2.16/1.00    v2_pre_topc(sK3)),
% 2.16/1.00    inference(cnf_transformation,[],[f53])).
% 2.16/1.00  
% 2.16/1.00  fof(f77,plain,(
% 2.16/1.00    v8_pre_topc(sK3)),
% 2.16/1.00    inference(cnf_transformation,[],[f53])).
% 2.16/1.00  
% 2.16/1.00  fof(f79,plain,(
% 2.16/1.00    v4_orders_2(sK3)),
% 2.16/1.00    inference(cnf_transformation,[],[f53])).
% 2.16/1.00  
% 2.16/1.00  fof(f81,plain,(
% 2.16/1.00    v1_lattice3(sK3)),
% 2.16/1.00    inference(cnf_transformation,[],[f53])).
% 2.16/1.00  
% 2.16/1.00  fof(f83,plain,(
% 2.16/1.00    v1_compts_1(sK3)),
% 2.16/1.00    inference(cnf_transformation,[],[f53])).
% 2.16/1.00  
% 2.16/1.00  fof(f86,plain,(
% 2.16/1.00    ~v2_struct_0(sK5)),
% 2.16/1.00    inference(cnf_transformation,[],[f53])).
% 2.16/1.00  
% 2.16/1.00  fof(f87,plain,(
% 2.16/1.00    v4_orders_2(sK5)),
% 2.16/1.00    inference(cnf_transformation,[],[f53])).
% 2.16/1.00  
% 2.16/1.00  fof(f89,plain,(
% 2.16/1.00    l1_waybel_0(sK5,sK3)),
% 2.16/1.00    inference(cnf_transformation,[],[f53])).
% 2.16/1.00  
% 2.16/1.00  fof(f85,plain,(
% 2.16/1.00    m1_subset_1(sK4,u1_struct_0(sK3))),
% 2.16/1.00    inference(cnf_transformation,[],[f53])).
% 2.16/1.00  
% 2.16/1.00  fof(f74,plain,(
% 2.16/1.00    ( ! [X4,X2,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | m1_subset_1(sK2(X0),u1_struct_0(X0)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f49])).
% 2.16/1.00  
% 2.16/1.00  fof(f99,plain,(
% 2.16/1.00    ( ! [X4,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | m1_subset_1(sK2(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.16/1.00    inference(equality_resolution,[],[f74])).
% 2.16/1.00  
% 2.16/1.00  fof(f7,axiom,(
% 2.16/1.00    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 2.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f18,plain,(
% 2.16/1.00    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 2.16/1.00    inference(pure_predicate_removal,[],[f7])).
% 2.16/1.00  
% 2.16/1.00  fof(f19,plain,(
% 2.16/1.00    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))))),
% 2.16/1.00    inference(pure_predicate_removal,[],[f18])).
% 2.16/1.00  
% 2.16/1.00  fof(f29,plain,(
% 2.16/1.00    ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 2.16/1.00    inference(ennf_transformation,[],[f19])).
% 2.16/1.00  
% 2.16/1.00  fof(f30,plain,(
% 2.16/1.00    ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 2.16/1.00    inference(flattening,[],[f29])).
% 2.16/1.00  
% 2.16/1.00  fof(f68,plain,(
% 2.16/1.00    ( ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f30])).
% 2.16/1.00  
% 2.16/1.00  fof(f3,axiom,(
% 2.16/1.00    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 2.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f22,plain,(
% 2.16/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 2.16/1.00    inference(ennf_transformation,[],[f3])).
% 2.16/1.00  
% 2.16/1.00  fof(f56,plain,(
% 2.16/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f22])).
% 2.16/1.00  
% 2.16/1.00  fof(f2,axiom,(
% 2.16/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f21,plain,(
% 2.16/1.00    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/1.00    inference(ennf_transformation,[],[f2])).
% 2.16/1.00  
% 2.16/1.00  fof(f55,plain,(
% 2.16/1.00    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.16/1.00    inference(cnf_transformation,[],[f21])).
% 2.16/1.00  
% 2.16/1.00  fof(f1,axiom,(
% 2.16/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f20,plain,(
% 2.16/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/1.00    inference(ennf_transformation,[],[f1])).
% 2.16/1.00  
% 2.16/1.00  fof(f54,plain,(
% 2.16/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.16/1.00    inference(cnf_transformation,[],[f20])).
% 2.16/1.00  
% 2.16/1.00  fof(f9,axiom,(
% 2.16/1.00    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (v1_relat_1(X1) => k1_yellow_0(X0,k2_relat_1(X1)) = k4_yellow_2(X0,X1)))),
% 2.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f33,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : (k1_yellow_0(X0,k2_relat_1(X1)) = k4_yellow_2(X0,X1) | ~v1_relat_1(X1)) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 2.16/1.00    inference(ennf_transformation,[],[f9])).
% 2.16/1.00  
% 2.16/1.00  fof(f34,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : (k1_yellow_0(X0,k2_relat_1(X1)) = k4_yellow_2(X0,X1) | ~v1_relat_1(X1)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 2.16/1.00    inference(flattening,[],[f33])).
% 2.16/1.00  
% 2.16/1.00  fof(f70,plain,(
% 2.16/1.00    ( ! [X0,X1] : (k1_yellow_0(X0,k2_relat_1(X1)) = k4_yellow_2(X0,X1) | ~v1_relat_1(X1) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f34])).
% 2.16/1.00  
% 2.16/1.00  fof(f8,axiom,(
% 2.16/1.00    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (l1_waybel_0(X1,X0) => k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1))))),
% 2.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f31,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : (k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0)) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 2.16/1.00    inference(ennf_transformation,[],[f8])).
% 2.16/1.00  
% 2.16/1.00  fof(f32,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : (k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 2.16/1.00    inference(flattening,[],[f31])).
% 2.16/1.00  
% 2.16/1.00  fof(f69,plain,(
% 2.16/1.00    ( ! [X0,X1] : (k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f32])).
% 2.16/1.00  
% 2.16/1.00  fof(f64,plain,(
% 2.16/1.00    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X2) = X1 | ~r1_orders_2(X0,X1,sK0(X0,X1,X2)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f44])).
% 2.16/1.00  
% 2.16/1.00  fof(f11,axiom,(
% 2.16/1.00    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & v10_waybel_0(X1,X0) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3))))))),
% 2.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f36,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | (~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.16/1.00    inference(ennf_transformation,[],[f11])).
% 2.16/1.00  
% 2.16/1.00  fof(f37,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.16/1.00    inference(flattening,[],[f36])).
% 2.16/1.00  
% 2.16/1.00  fof(f45,plain,(
% 2.16/1.00    ! [X0] : (? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0) & m1_subset_1(sK1(X0),u1_struct_0(X0))))),
% 2.16/1.00    introduced(choice_axiom,[])).
% 2.16/1.00  
% 2.16/1.00  fof(f46,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | (~v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0) & m1_subset_1(sK1(X0),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.16/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f45])).
% 2.16/1.00  
% 2.16/1.00  fof(f73,plain,(
% 2.16/1.00    ( ! [X2,X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f46])).
% 2.16/1.00  
% 2.16/1.00  fof(f96,plain,(
% 2.16/1.00    ( ! [X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v10_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.16/1.00    inference(equality_resolution,[],[f73])).
% 2.16/1.00  
% 2.16/1.00  fof(f91,plain,(
% 2.16/1.00    v10_waybel_0(sK5,sK3)),
% 2.16/1.00    inference(cnf_transformation,[],[f53])).
% 2.16/1.00  
% 2.16/1.00  fof(f72,plain,(
% 2.16/1.00    ( ! [X2,X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | m1_subset_1(sK1(X0),u1_struct_0(X0)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f46])).
% 2.16/1.00  
% 2.16/1.00  fof(f97,plain,(
% 2.16/1.00    ( ! [X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v10_waybel_0(X1,X0) | m1_subset_1(sK1(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.16/1.00    inference(equality_resolution,[],[f72])).
% 2.16/1.00  
% 2.16/1.00  fof(f93,plain,(
% 2.16/1.00    k1_waybel_2(sK3,sK5) != sK4),
% 2.16/1.00    inference(cnf_transformation,[],[f53])).
% 2.16/1.00  
% 2.16/1.00  cnf(c_11,plain,
% 2.16/1.00      ( ~ r2_lattice3(X0,X1,X2)
% 2.16/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.16/1.00      | m1_subset_1(sK0(X0,X2,X1),u1_struct_0(X0))
% 2.16/1.00      | ~ v5_orders_2(X0)
% 2.16/1.00      | ~ l1_orders_2(X0)
% 2.16/1.00      | k1_yellow_0(X0,X1) = X2 ),
% 2.16/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_35,negated_conjecture,
% 2.16/1.00      ( v5_orders_2(sK3) ),
% 2.16/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1125,plain,
% 2.16/1.00      ( ~ r2_lattice3(X0,X1,X2)
% 2.16/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.16/1.00      | m1_subset_1(sK0(X0,X2,X1),u1_struct_0(X0))
% 2.16/1.00      | ~ l1_orders_2(X0)
% 2.16/1.00      | k1_yellow_0(X0,X1) = X2
% 2.16/1.00      | sK3 != X0 ),
% 2.16/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_35]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1126,plain,
% 2.16/1.00      ( ~ r2_lattice3(sK3,X0,X1)
% 2.16/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.16/1.00      | m1_subset_1(sK0(sK3,X1,X0),u1_struct_0(sK3))
% 2.16/1.00      | ~ l1_orders_2(sK3)
% 2.16/1.00      | k1_yellow_0(sK3,X0) = X1 ),
% 2.16/1.00      inference(unflattening,[status(thm)],[c_1125]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_31,negated_conjecture,
% 2.16/1.00      ( l1_waybel_9(sK3) ),
% 2.16/1.00      inference(cnf_transformation,[],[f84]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_17,plain,
% 2.16/1.00      ( ~ l1_waybel_9(X0) | l1_orders_2(X0) ),
% 2.16/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_72,plain,
% 2.16/1.00      ( ~ l1_waybel_9(sK3) | l1_orders_2(sK3) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1130,plain,
% 2.16/1.00      ( m1_subset_1(sK0(sK3,X1,X0),u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.16/1.00      | ~ r2_lattice3(sK3,X0,X1)
% 2.16/1.00      | k1_yellow_0(sK3,X0) = X1 ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_1126,c_31,c_72]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1131,plain,
% 2.16/1.00      ( ~ r2_lattice3(sK3,X0,X1)
% 2.16/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.16/1.00      | m1_subset_1(sK0(sK3,X1,X0),u1_struct_0(sK3))
% 2.16/1.00      | k1_yellow_0(sK3,X0) = X1 ),
% 2.16/1.00      inference(renaming,[status(thm)],[c_1130]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2224,plain,
% 2.16/1.00      ( ~ r2_lattice3(sK3,X0_69,X0_67)
% 2.16/1.00      | ~ m1_subset_1(X0_67,u1_struct_0(sK3))
% 2.16/1.00      | m1_subset_1(sK0(sK3,X0_67,X0_69),u1_struct_0(sK3))
% 2.16/1.00      | k1_yellow_0(sK3,X0_69) = X0_67 ),
% 2.16/1.00      inference(subtyping,[status(esa)],[c_1131]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2678,plain,
% 2.16/1.00      ( k1_yellow_0(sK3,X0_69) = X0_67
% 2.16/1.00      | r2_lattice3(sK3,X0_69,X0_67) != iProver_top
% 2.16/1.00      | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top
% 2.16/1.00      | m1_subset_1(sK0(sK3,X0_67,X0_69),u1_struct_0(sK3)) = iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_2224]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_10,plain,
% 2.16/1.00      ( ~ r2_lattice3(X0,X1,X2)
% 2.16/1.00      | r2_lattice3(X0,X1,sK0(X0,X2,X1))
% 2.16/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.16/1.00      | ~ v5_orders_2(X0)
% 2.16/1.00      | ~ l1_orders_2(X0)
% 2.16/1.00      | k1_yellow_0(X0,X1) = X2 ),
% 2.16/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1149,plain,
% 2.16/1.00      ( ~ r2_lattice3(X0,X1,X2)
% 2.16/1.00      | r2_lattice3(X0,X1,sK0(X0,X2,X1))
% 2.16/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.16/1.00      | ~ l1_orders_2(X0)
% 2.16/1.00      | k1_yellow_0(X0,X1) = X2
% 2.16/1.00      | sK3 != X0 ),
% 2.16/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_35]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1150,plain,
% 2.16/1.00      ( ~ r2_lattice3(sK3,X0,X1)
% 2.16/1.00      | r2_lattice3(sK3,X0,sK0(sK3,X1,X0))
% 2.16/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.16/1.00      | ~ l1_orders_2(sK3)
% 2.16/1.00      | k1_yellow_0(sK3,X0) = X1 ),
% 2.16/1.00      inference(unflattening,[status(thm)],[c_1149]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1154,plain,
% 2.16/1.00      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.16/1.00      | r2_lattice3(sK3,X0,sK0(sK3,X1,X0))
% 2.16/1.00      | ~ r2_lattice3(sK3,X0,X1)
% 2.16/1.00      | k1_yellow_0(sK3,X0) = X1 ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_1150,c_31,c_72]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1155,plain,
% 2.16/1.00      ( ~ r2_lattice3(sK3,X0,X1)
% 2.16/1.00      | r2_lattice3(sK3,X0,sK0(sK3,X1,X0))
% 2.16/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.16/1.00      | k1_yellow_0(sK3,X0) = X1 ),
% 2.16/1.00      inference(renaming,[status(thm)],[c_1154]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2223,plain,
% 2.16/1.00      ( ~ r2_lattice3(sK3,X0_69,X0_67)
% 2.16/1.00      | r2_lattice3(sK3,X0_69,sK0(sK3,X0_67,X0_69))
% 2.16/1.00      | ~ m1_subset_1(X0_67,u1_struct_0(sK3))
% 2.16/1.00      | k1_yellow_0(sK3,X0_69) = X0_67 ),
% 2.16/1.00      inference(subtyping,[status(esa)],[c_1155]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2679,plain,
% 2.16/1.00      ( k1_yellow_0(sK3,X0_69) = X0_67
% 2.16/1.00      | r2_lattice3(sK3,X0_69,X0_67) != iProver_top
% 2.16/1.00      | r2_lattice3(sK3,X0_69,sK0(sK3,X0_67,X0_69)) = iProver_top
% 2.16/1.00      | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_2223]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_4,plain,
% 2.16/1.00      ( r1_orders_2(X0,X1,X2)
% 2.16/1.00      | ~ r3_orders_2(X0,X1,X2)
% 2.16/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.16/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.16/1.00      | v2_struct_0(X0)
% 2.16/1.00      | ~ v3_orders_2(X0)
% 2.16/1.00      | ~ l1_orders_2(X0) ),
% 2.16/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_37,negated_conjecture,
% 2.16/1.00      ( v3_orders_2(sK3) ),
% 2.16/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_682,plain,
% 2.16/1.00      ( r1_orders_2(X0,X1,X2)
% 2.16/1.00      | ~ r3_orders_2(X0,X1,X2)
% 2.16/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.16/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.16/1.00      | v2_struct_0(X0)
% 2.16/1.00      | ~ l1_orders_2(X0)
% 2.16/1.00      | sK3 != X0 ),
% 2.16/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_37]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_683,plain,
% 2.16/1.00      ( r1_orders_2(sK3,X0,X1)
% 2.16/1.00      | ~ r3_orders_2(sK3,X0,X1)
% 2.16/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.16/1.00      | v2_struct_0(sK3)
% 2.16/1.00      | ~ l1_orders_2(sK3) ),
% 2.16/1.00      inference(unflattening,[status(thm)],[c_682]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_33,negated_conjecture,
% 2.16/1.00      ( v2_lattice3(sK3) ),
% 2.16/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_5,plain,
% 2.16/1.00      ( ~ v2_lattice3(X0) | ~ v2_struct_0(X0) | ~ l1_orders_2(X0) ),
% 2.16/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_108,plain,
% 2.16/1.00      ( ~ v2_lattice3(sK3) | ~ v2_struct_0(sK3) | ~ l1_orders_2(sK3) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_687,plain,
% 2.16/1.00      ( r1_orders_2(sK3,X0,X1)
% 2.16/1.00      | ~ r3_orders_2(sK3,X0,X1)
% 2.16/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_683,c_33,c_31,c_72,c_108]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_688,plain,
% 2.16/1.00      ( r1_orders_2(sK3,X0,X1)
% 2.16/1.00      | ~ r3_orders_2(sK3,X0,X1)
% 2.16/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
% 2.16/1.00      inference(renaming,[status(thm)],[c_687]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_23,negated_conjecture,
% 2.16/1.00      ( r3_waybel_9(sK3,sK5,sK4) ),
% 2.16/1.00      inference(cnf_transformation,[],[f92]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_27,negated_conjecture,
% 2.16/1.00      ( v7_waybel_0(sK5) ),
% 2.16/1.00      inference(cnf_transformation,[],[f88]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_20,plain,
% 2.16/1.00      ( ~ v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0)
% 2.16/1.00      | ~ r3_waybel_9(X0,X1,X2)
% 2.16/1.00      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 2.16/1.00      | r3_orders_2(X0,X2,X3)
% 2.16/1.00      | ~ l1_waybel_0(X1,X0)
% 2.16/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.16/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.16/1.00      | ~ v2_pre_topc(X0)
% 2.16/1.00      | ~ v8_pre_topc(X0)
% 2.16/1.00      | ~ v1_lattice3(X0)
% 2.16/1.00      | ~ v1_compts_1(X0)
% 2.16/1.00      | ~ v4_orders_2(X1)
% 2.16/1.00      | ~ v4_orders_2(X0)
% 2.16/1.00      | ~ v7_waybel_0(X1)
% 2.16/1.00      | ~ l1_waybel_9(X0)
% 2.16/1.00      | ~ v5_orders_2(X0)
% 2.16/1.00      | ~ v2_lattice3(X0)
% 2.16/1.00      | v2_struct_0(X1)
% 2.16/1.00      | ~ v3_orders_2(X0) ),
% 2.16/1.00      inference(cnf_transformation,[],[f98]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_25,negated_conjecture,
% 2.16/1.00      ( v5_pre_topc(k4_waybel_1(sK3,X0),sK3,sK3)
% 2.16/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 2.16/1.00      inference(cnf_transformation,[],[f90]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_531,plain,
% 2.16/1.00      ( ~ r3_waybel_9(X0,X1,X2)
% 2.16/1.00      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 2.16/1.00      | r3_orders_2(X0,X2,X3)
% 2.16/1.00      | ~ l1_waybel_0(X1,X0)
% 2.16/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.16/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.16/1.00      | ~ m1_subset_1(X4,u1_struct_0(sK3))
% 2.16/1.00      | ~ v2_pre_topc(X0)
% 2.16/1.00      | ~ v8_pre_topc(X0)
% 2.16/1.00      | ~ v1_lattice3(X0)
% 2.16/1.00      | ~ v1_compts_1(X0)
% 2.16/1.00      | ~ v4_orders_2(X1)
% 2.16/1.00      | ~ v4_orders_2(X0)
% 2.16/1.00      | ~ v7_waybel_0(X1)
% 2.16/1.00      | ~ l1_waybel_9(X0)
% 2.16/1.00      | ~ v5_orders_2(X0)
% 2.16/1.00      | ~ v2_lattice3(X0)
% 2.16/1.00      | v2_struct_0(X1)
% 2.16/1.00      | ~ v3_orders_2(X0)
% 2.16/1.00      | k4_waybel_1(X0,sK2(X0)) != k4_waybel_1(sK3,X4)
% 2.16/1.00      | sK3 != X0 ),
% 2.16/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_25]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_532,plain,
% 2.16/1.00      ( ~ r3_waybel_9(sK3,X0,X1)
% 2.16/1.00      | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
% 2.16/1.00      | r3_orders_2(sK3,X1,X2)
% 2.16/1.00      | ~ l1_waybel_0(X0,sK3)
% 2.16/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 2.16/1.00      | ~ v2_pre_topc(sK3)
% 2.16/1.00      | ~ v8_pre_topc(sK3)
% 2.16/1.00      | ~ v1_lattice3(sK3)
% 2.16/1.00      | ~ v1_compts_1(sK3)
% 2.16/1.00      | ~ v4_orders_2(X0)
% 2.16/1.00      | ~ v4_orders_2(sK3)
% 2.16/1.00      | ~ v7_waybel_0(X0)
% 2.16/1.00      | ~ l1_waybel_9(sK3)
% 2.16/1.00      | ~ v5_orders_2(sK3)
% 2.16/1.00      | ~ v2_lattice3(sK3)
% 2.16/1.00      | v2_struct_0(X0)
% 2.16/1.00      | ~ v3_orders_2(sK3)
% 2.16/1.00      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X3) ),
% 2.16/1.00      inference(unflattening,[status(thm)],[c_531]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_39,negated_conjecture,
% 2.16/1.00      ( v2_pre_topc(sK3) ),
% 2.16/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_38,negated_conjecture,
% 2.16/1.00      ( v8_pre_topc(sK3) ),
% 2.16/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_36,negated_conjecture,
% 2.16/1.00      ( v4_orders_2(sK3) ),
% 2.16/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_34,negated_conjecture,
% 2.16/1.00      ( v1_lattice3(sK3) ),
% 2.16/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_32,negated_conjecture,
% 2.16/1.00      ( v1_compts_1(sK3) ),
% 2.16/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_536,plain,
% 2.16/1.00      ( v2_struct_0(X0)
% 2.16/1.00      | ~ v4_orders_2(X0)
% 2.16/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 2.16/1.00      | ~ l1_waybel_0(X0,sK3)
% 2.16/1.00      | r3_orders_2(sK3,X1,X2)
% 2.16/1.00      | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
% 2.16/1.00      | ~ r3_waybel_9(sK3,X0,X1)
% 2.16/1.00      | ~ v7_waybel_0(X0)
% 2.16/1.00      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X3) ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_532,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_31]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_537,plain,
% 2.16/1.00      ( ~ r3_waybel_9(sK3,X0,X1)
% 2.16/1.00      | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
% 2.16/1.00      | r3_orders_2(sK3,X1,X2)
% 2.16/1.00      | ~ l1_waybel_0(X0,sK3)
% 2.16/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.16/1.00      | ~ v4_orders_2(X0)
% 2.16/1.00      | ~ v7_waybel_0(X0)
% 2.16/1.00      | v2_struct_0(X0)
% 2.16/1.00      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X3) ),
% 2.16/1.00      inference(renaming,[status(thm)],[c_536]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_770,plain,
% 2.16/1.00      ( ~ r3_waybel_9(sK3,X0,X1)
% 2.16/1.00      | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
% 2.16/1.00      | r3_orders_2(sK3,X1,X2)
% 2.16/1.00      | ~ l1_waybel_0(X0,sK3)
% 2.16/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.16/1.00      | ~ v4_orders_2(X0)
% 2.16/1.00      | v2_struct_0(X0)
% 2.16/1.00      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X3)
% 2.16/1.00      | sK5 != X0 ),
% 2.16/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_537]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_771,plain,
% 2.16/1.00      ( ~ r3_waybel_9(sK3,sK5,X0)
% 2.16/1.00      | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
% 2.16/1.00      | r3_orders_2(sK3,X0,X1)
% 2.16/1.00      | ~ l1_waybel_0(sK5,sK3)
% 2.16/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.16/1.00      | ~ v4_orders_2(sK5)
% 2.16/1.00      | v2_struct_0(sK5)
% 2.16/1.00      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X2) ),
% 2.16/1.00      inference(unflattening,[status(thm)],[c_770]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_29,negated_conjecture,
% 2.16/1.00      ( ~ v2_struct_0(sK5) ),
% 2.16/1.00      inference(cnf_transformation,[],[f86]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_28,negated_conjecture,
% 2.16/1.00      ( v4_orders_2(sK5) ),
% 2.16/1.00      inference(cnf_transformation,[],[f87]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_26,negated_conjecture,
% 2.16/1.00      ( l1_waybel_0(sK5,sK3) ),
% 2.16/1.00      inference(cnf_transformation,[],[f89]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_775,plain,
% 2.16/1.00      ( r3_orders_2(sK3,X0,X1)
% 2.16/1.00      | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
% 2.16/1.00      | ~ r3_waybel_9(sK3,sK5,X0)
% 2.16/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.16/1.00      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X2) ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_771,c_29,c_28,c_26]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_776,plain,
% 2.16/1.00      ( ~ r3_waybel_9(sK3,sK5,X0)
% 2.16/1.00      | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
% 2.16/1.00      | r3_orders_2(sK3,X0,X1)
% 2.16/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.16/1.00      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X2) ),
% 2.16/1.00      inference(renaming,[status(thm)],[c_775]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_910,plain,
% 2.16/1.00      ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 2.16/1.00      | r3_orders_2(sK3,X1,X0)
% 2.16/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.16/1.00      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X2)
% 2.16/1.00      | sK4 != X1
% 2.16/1.00      | sK5 != sK5
% 2.16/1.00      | sK3 != sK3 ),
% 2.16/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_776]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_911,plain,
% 2.16/1.00      ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 2.16/1.00      | r3_orders_2(sK3,sK4,X0)
% 2.16/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 2.16/1.00      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1) ),
% 2.16/1.00      inference(unflattening,[status(thm)],[c_910]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_30,negated_conjecture,
% 2.16/1.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 2.16/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_915,plain,
% 2.16/1.00      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.16/1.00      | r3_orders_2(sK3,sK4,X0)
% 2.16/1.00      | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 2.16/1.00      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1) ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_911,c_30]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_916,plain,
% 2.16/1.00      ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 2.16/1.00      | r3_orders_2(sK3,sK4,X0)
% 2.16/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.16/1.00      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1) ),
% 2.16/1.00      inference(renaming,[status(thm)],[c_915]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1039,plain,
% 2.16/1.00      ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 2.16/1.00      | r1_orders_2(sK3,X1,X2)
% 2.16/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 2.16/1.00      | X0 != X2
% 2.16/1.00      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X3)
% 2.16/1.00      | sK4 != X1
% 2.16/1.00      | sK3 != sK3 ),
% 2.16/1.00      inference(resolution_lifted,[status(thm)],[c_688,c_916]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1040,plain,
% 2.16/1.00      ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 2.16/1.00      | r1_orders_2(sK3,sK4,X0)
% 2.16/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 2.16/1.00      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1) ),
% 2.16/1.00      inference(unflattening,[status(thm)],[c_1039]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1044,plain,
% 2.16/1.00      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.16/1.00      | r1_orders_2(sK3,sK4,X0)
% 2.16/1.00      | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 2.16/1.00      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1) ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_1040,c_30]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1045,plain,
% 2.16/1.00      ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 2.16/1.00      | r1_orders_2(sK3,sK4,X0)
% 2.16/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.16/1.00      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1) ),
% 2.16/1.00      inference(renaming,[status(thm)],[c_1044]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2227,plain,
% 2.16/1.00      ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_67)
% 2.16/1.00      | r1_orders_2(sK3,sK4,X0_67)
% 2.16/1.00      | ~ m1_subset_1(X1_67,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X0_67,u1_struct_0(sK3))
% 2.16/1.00      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1_67) ),
% 2.16/1.00      inference(subtyping,[status(esa)],[c_1045]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2239,plain,
% 2.16/1.00      ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_67)
% 2.16/1.00      | r1_orders_2(sK3,sK4,X0_67)
% 2.16/1.00      | ~ m1_subset_1(X0_67,u1_struct_0(sK3))
% 2.16/1.00      | ~ sP1_iProver_split ),
% 2.16/1.00      inference(splitting,
% 2.16/1.00                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.16/1.00                [c_2227]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2674,plain,
% 2.16/1.00      ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_67) != iProver_top
% 2.16/1.00      | r1_orders_2(sK3,sK4,X0_67) = iProver_top
% 2.16/1.00      | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top
% 2.16/1.00      | sP1_iProver_split != iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_2239]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_21,plain,
% 2.16/1.00      ( ~ r3_waybel_9(X0,X1,X2)
% 2.16/1.00      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 2.16/1.00      | r3_orders_2(X0,X2,X3)
% 2.16/1.00      | ~ l1_waybel_0(X1,X0)
% 2.16/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.16/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.16/1.00      | m1_subset_1(sK2(X0),u1_struct_0(X0))
% 2.16/1.00      | ~ v2_pre_topc(X0)
% 2.16/1.00      | ~ v8_pre_topc(X0)
% 2.16/1.00      | ~ v1_lattice3(X0)
% 2.16/1.00      | ~ v1_compts_1(X0)
% 2.16/1.00      | ~ v4_orders_2(X1)
% 2.16/1.00      | ~ v4_orders_2(X0)
% 2.16/1.00      | ~ v7_waybel_0(X1)
% 2.16/1.00      | ~ l1_waybel_9(X0)
% 2.16/1.00      | ~ v5_orders_2(X0)
% 2.16/1.00      | ~ v2_lattice3(X0)
% 2.16/1.00      | v2_struct_0(X1)
% 2.16/1.00      | ~ v3_orders_2(X0) ),
% 2.16/1.00      inference(cnf_transformation,[],[f99]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_607,plain,
% 2.16/1.00      ( ~ r3_waybel_9(X0,X1,X2)
% 2.16/1.00      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 2.16/1.00      | r3_orders_2(X0,X2,X3)
% 2.16/1.00      | ~ l1_waybel_0(X1,X0)
% 2.16/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.16/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.16/1.00      | m1_subset_1(sK2(X0),u1_struct_0(X0))
% 2.16/1.00      | ~ v2_pre_topc(X0)
% 2.16/1.00      | ~ v8_pre_topc(X0)
% 2.16/1.00      | ~ v1_lattice3(X0)
% 2.16/1.00      | ~ v4_orders_2(X1)
% 2.16/1.00      | ~ v4_orders_2(X0)
% 2.16/1.00      | ~ v7_waybel_0(X1)
% 2.16/1.00      | ~ l1_waybel_9(X0)
% 2.16/1.00      | ~ v5_orders_2(X0)
% 2.16/1.00      | ~ v2_lattice3(X0)
% 2.16/1.00      | v2_struct_0(X1)
% 2.16/1.00      | ~ v3_orders_2(X0)
% 2.16/1.00      | sK3 != X0 ),
% 2.16/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_32]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_608,plain,
% 2.16/1.00      ( ~ r3_waybel_9(sK3,X0,X1)
% 2.16/1.00      | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
% 2.16/1.00      | r3_orders_2(sK3,X1,X2)
% 2.16/1.00      | ~ l1_waybel_0(X0,sK3)
% 2.16/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 2.16/1.00      | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
% 2.16/1.00      | ~ v2_pre_topc(sK3)
% 2.16/1.00      | ~ v8_pre_topc(sK3)
% 2.16/1.00      | ~ v1_lattice3(sK3)
% 2.16/1.00      | ~ v4_orders_2(X0)
% 2.16/1.00      | ~ v4_orders_2(sK3)
% 2.16/1.00      | ~ v7_waybel_0(X0)
% 2.16/1.00      | ~ l1_waybel_9(sK3)
% 2.16/1.00      | ~ v5_orders_2(sK3)
% 2.16/1.00      | ~ v2_lattice3(sK3)
% 2.16/1.00      | v2_struct_0(X0)
% 2.16/1.00      | ~ v3_orders_2(sK3) ),
% 2.16/1.00      inference(unflattening,[status(thm)],[c_607]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_612,plain,
% 2.16/1.00      ( v2_struct_0(X0)
% 2.16/1.00      | ~ v4_orders_2(X0)
% 2.16/1.00      | ~ r3_waybel_9(sK3,X0,X1)
% 2.16/1.00      | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
% 2.16/1.00      | r3_orders_2(sK3,X1,X2)
% 2.16/1.00      | ~ l1_waybel_0(X0,sK3)
% 2.16/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 2.16/1.00      | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
% 2.16/1.00      | ~ v7_waybel_0(X0) ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_608,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_31]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_613,plain,
% 2.16/1.00      ( ~ r3_waybel_9(sK3,X0,X1)
% 2.16/1.00      | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
% 2.16/1.00      | r3_orders_2(sK3,X1,X2)
% 2.16/1.00      | ~ l1_waybel_0(X0,sK3)
% 2.16/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.16/1.00      | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
% 2.16/1.00      | ~ v4_orders_2(X0)
% 2.16/1.00      | ~ v7_waybel_0(X0)
% 2.16/1.00      | v2_struct_0(X0) ),
% 2.16/1.00      inference(renaming,[status(thm)],[c_612]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_740,plain,
% 2.16/1.00      ( ~ r3_waybel_9(sK3,X0,X1)
% 2.16/1.00      | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
% 2.16/1.00      | r3_orders_2(sK3,X1,X2)
% 2.16/1.00      | ~ l1_waybel_0(X0,sK3)
% 2.16/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.16/1.00      | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
% 2.16/1.00      | ~ v4_orders_2(X0)
% 2.16/1.00      | v2_struct_0(X0)
% 2.16/1.00      | sK5 != X0 ),
% 2.16/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_613]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_741,plain,
% 2.16/1.00      ( ~ r3_waybel_9(sK3,sK5,X0)
% 2.16/1.00      | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
% 2.16/1.00      | r3_orders_2(sK3,X0,X1)
% 2.16/1.00      | ~ l1_waybel_0(sK5,sK3)
% 2.16/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.16/1.00      | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
% 2.16/1.00      | ~ v4_orders_2(sK5)
% 2.16/1.00      | v2_struct_0(sK5) ),
% 2.16/1.00      inference(unflattening,[status(thm)],[c_740]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_745,plain,
% 2.16/1.00      ( r3_orders_2(sK3,X0,X1)
% 2.16/1.00      | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
% 2.16/1.00      | ~ r3_waybel_9(sK3,sK5,X0)
% 2.16/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.16/1.00      | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_741,c_29,c_28,c_26]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_746,plain,
% 2.16/1.00      ( ~ r3_waybel_9(sK3,sK5,X0)
% 2.16/1.00      | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
% 2.16/1.00      | r3_orders_2(sK3,X0,X1)
% 2.16/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.16/1.00      | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) ),
% 2.16/1.00      inference(renaming,[status(thm)],[c_745]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_937,plain,
% 2.16/1.00      ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 2.16/1.00      | r3_orders_2(sK3,X1,X0)
% 2.16/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.16/1.00      | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
% 2.16/1.00      | sK4 != X1
% 2.16/1.00      | sK5 != sK5
% 2.16/1.00      | sK3 != sK3 ),
% 2.16/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_746]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_938,plain,
% 2.16/1.00      ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 2.16/1.00      | r3_orders_2(sK3,sK4,X0)
% 2.16/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.16/1.00      | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 2.16/1.00      inference(unflattening,[status(thm)],[c_937]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_942,plain,
% 2.16/1.00      ( m1_subset_1(sK2(sK3),u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.16/1.00      | r3_orders_2(sK3,sK4,X0)
% 2.16/1.00      | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0) ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_938,c_30]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_943,plain,
% 2.16/1.00      ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 2.16/1.00      | r3_orders_2(sK3,sK4,X0)
% 2.16/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.16/1.00      | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) ),
% 2.16/1.00      inference(renaming,[status(thm)],[c_942]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1015,plain,
% 2.16/1.00      ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 2.16/1.00      | r1_orders_2(sK3,X1,X2)
% 2.16/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.16/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 2.16/1.00      | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
% 2.16/1.00      | X0 != X2
% 2.16/1.00      | sK4 != X1
% 2.16/1.00      | sK3 != sK3 ),
% 2.16/1.00      inference(resolution_lifted,[status(thm)],[c_688,c_943]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1016,plain,
% 2.16/1.00      ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 2.16/1.00      | r1_orders_2(sK3,sK4,X0)
% 2.16/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.16/1.01      | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
% 2.16/1.01      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 2.16/1.01      inference(unflattening,[status(thm)],[c_1015]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_1020,plain,
% 2.16/1.01      ( m1_subset_1(sK2(sK3),u1_struct_0(sK3))
% 2.16/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.16/1.01      | r1_orders_2(sK3,sK4,X0)
% 2.16/1.01      | ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0) ),
% 2.16/1.01      inference(global_propositional_subsumption,
% 2.16/1.01                [status(thm)],
% 2.16/1.01                [c_1016,c_30]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_1021,plain,
% 2.16/1.01      ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 2.16/1.01      | r1_orders_2(sK3,sK4,X0)
% 2.16/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.16/1.01      | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) ),
% 2.16/1.01      inference(renaming,[status(thm)],[c_1020]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_2228,plain,
% 2.16/1.01      ( ~ r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_67)
% 2.16/1.01      | r1_orders_2(sK3,sK4,X0_67)
% 2.16/1.01      | ~ m1_subset_1(X0_67,u1_struct_0(sK3))
% 2.16/1.01      | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) ),
% 2.16/1.01      inference(subtyping,[status(esa)],[c_1021]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_2306,plain,
% 2.16/1.01      ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_67) != iProver_top
% 2.16/1.01      | r1_orders_2(sK3,sK4,X0_67) = iProver_top
% 2.16/1.01      | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top
% 2.16/1.01      | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) = iProver_top ),
% 2.16/1.01      inference(predicate_to_equality,[status(thm)],[c_2228]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_2240,plain,
% 2.16/1.01      ( sP1_iProver_split | sP0_iProver_split ),
% 2.16/1.01      inference(splitting,
% 2.16/1.01                [splitting(split),new_symbols(definition,[])],
% 2.16/1.01                [c_2227]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_2309,plain,
% 2.16/1.01      ( sP1_iProver_split = iProver_top
% 2.16/1.01      | sP0_iProver_split = iProver_top ),
% 2.16/1.01      inference(predicate_to_equality,[status(thm)],[c_2240]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_2310,plain,
% 2.16/1.01      ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_67) != iProver_top
% 2.16/1.01      | r1_orders_2(sK3,sK4,X0_67) = iProver_top
% 2.16/1.01      | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top
% 2.16/1.01      | sP1_iProver_split != iProver_top ),
% 2.16/1.01      inference(predicate_to_equality,[status(thm)],[c_2239]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_2238,plain,
% 2.16/1.01      ( ~ m1_subset_1(X0_67,u1_struct_0(sK3))
% 2.16/1.01      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X0_67)
% 2.16/1.01      | ~ sP0_iProver_split ),
% 2.16/1.01      inference(splitting,
% 2.16/1.01                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.16/1.01                [c_2227]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_2675,plain,
% 2.16/1.01      ( k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X0_67)
% 2.16/1.01      | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top
% 2.16/1.01      | sP0_iProver_split != iProver_top ),
% 2.16/1.01      inference(predicate_to_equality,[status(thm)],[c_2238]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_3464,plain,
% 2.16/1.01      ( m1_subset_1(sK2(sK3),u1_struct_0(sK3)) != iProver_top
% 2.16/1.01      | sP0_iProver_split != iProver_top ),
% 2.16/1.01      inference(equality_resolution,[status(thm)],[c_2675]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_3509,plain,
% 2.16/1.01      ( m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top
% 2.16/1.01      | r1_orders_2(sK3,sK4,X0_67) = iProver_top
% 2.16/1.01      | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_67) != iProver_top ),
% 2.16/1.01      inference(global_propositional_subsumption,
% 2.16/1.01                [status(thm)],
% 2.16/1.01                [c_2674,c_2306,c_2309,c_2310,c_3464]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_3510,plain,
% 2.16/1.01      ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_67) != iProver_top
% 2.16/1.01      | r1_orders_2(sK3,sK4,X0_67) = iProver_top
% 2.16/1.01      | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top ),
% 2.16/1.01      inference(renaming,[status(thm)],[c_3509]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_14,plain,
% 2.16/1.01      ( ~ l1_waybel_0(X0,X1)
% 2.16/1.01      | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.16/1.01      | ~ l1_struct_0(X1) ),
% 2.16/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_2,plain,
% 2.16/1.01      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 2.16/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_432,plain,
% 2.16/1.01      ( ~ l1_waybel_0(X0,X1)
% 2.16/1.01      | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.16/1.01      | ~ l1_orders_2(X2)
% 2.16/1.01      | X2 != X1 ),
% 2.16/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_2]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_433,plain,
% 2.16/1.01      ( ~ l1_waybel_0(X0,X1)
% 2.16/1.01      | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.16/1.01      | ~ l1_orders_2(X1) ),
% 2.16/1.01      inference(unflattening,[status(thm)],[c_432]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_818,plain,
% 2.16/1.01      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
% 2.16/1.01      | ~ l1_orders_2(X0)
% 2.16/1.01      | sK5 != X1
% 2.16/1.01      | sK3 != X0 ),
% 2.16/1.01      inference(resolution_lifted,[status(thm)],[c_433,c_26]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_819,plain,
% 2.16/1.01      ( m1_subset_1(u1_waybel_0(sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 2.16/1.01      | ~ l1_orders_2(sK3) ),
% 2.16/1.01      inference(unflattening,[status(thm)],[c_818]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_821,plain,
% 2.16/1.01      ( m1_subset_1(u1_waybel_0(sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 2.16/1.01      inference(global_propositional_subsumption,
% 2.16/1.01                [status(thm)],
% 2.16/1.01                [c_819,c_31,c_72]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_2233,plain,
% 2.16/1.01      ( m1_subset_1(u1_waybel_0(sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 2.16/1.01      inference(subtyping,[status(esa)],[c_821]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_2668,plain,
% 2.16/1.01      ( m1_subset_1(u1_waybel_0(sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 2.16/1.01      inference(predicate_to_equality,[status(thm)],[c_2233]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_1,plain,
% 2.16/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.16/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.16/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_2236,plain,
% 2.16/1.01      ( ~ m1_subset_1(X0_67,k1_zfmisc_1(k2_zfmisc_1(X0_70,X1_70)))
% 2.16/1.01      | k2_relset_1(X0_70,X1_70,X0_67) = k2_relat_1(X0_67) ),
% 2.16/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_2666,plain,
% 2.16/1.01      ( k2_relset_1(X0_70,X1_70,X0_67) = k2_relat_1(X0_67)
% 2.16/1.01      | m1_subset_1(X0_67,k1_zfmisc_1(k2_zfmisc_1(X0_70,X1_70))) != iProver_top ),
% 2.16/1.01      inference(predicate_to_equality,[status(thm)],[c_2236]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_2927,plain,
% 2.16/1.01      ( k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)) = k2_relat_1(u1_waybel_0(sK3,sK5)) ),
% 2.16/1.01      inference(superposition,[status(thm)],[c_2668,c_2666]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_3515,plain,
% 2.16/1.01      ( r2_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_67) != iProver_top
% 2.16/1.01      | r1_orders_2(sK3,sK4,X0_67) = iProver_top
% 2.16/1.01      | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top ),
% 2.16/1.01      inference(light_normalisation,[status(thm)],[c_3510,c_2927]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_3523,plain,
% 2.16/1.01      ( k1_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = X0_67
% 2.16/1.01      | r2_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_67) != iProver_top
% 2.16/1.01      | r1_orders_2(sK3,sK4,sK0(sK3,X0_67,k2_relat_1(u1_waybel_0(sK3,sK5)))) = iProver_top
% 2.16/1.01      | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top
% 2.16/1.01      | m1_subset_1(sK0(sK3,X0_67,k2_relat_1(u1_waybel_0(sK3,sK5))),u1_struct_0(sK3)) != iProver_top ),
% 2.16/1.01      inference(superposition,[status(thm)],[c_2679,c_3515]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_0,plain,
% 2.16/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.16/1.01      | v1_relat_1(X0) ),
% 2.16/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_2237,plain,
% 2.16/1.01      ( ~ m1_subset_1(X0_67,k1_zfmisc_1(k2_zfmisc_1(X0_70,X1_70)))
% 2.16/1.01      | v1_relat_1(X0_67) ),
% 2.16/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_2665,plain,
% 2.16/1.01      ( m1_subset_1(X0_67,k1_zfmisc_1(k2_zfmisc_1(X0_70,X1_70))) != iProver_top
% 2.16/1.01      | v1_relat_1(X0_67) = iProver_top ),
% 2.16/1.01      inference(predicate_to_equality,[status(thm)],[c_2237]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_2922,plain,
% 2.16/1.01      ( v1_relat_1(u1_waybel_0(sK3,sK5)) = iProver_top ),
% 2.16/1.01      inference(superposition,[status(thm)],[c_2668,c_2665]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_16,plain,
% 2.16/1.01      ( v2_struct_0(X0)
% 2.16/1.01      | ~ l1_orders_2(X0)
% 2.16/1.01      | ~ v1_relat_1(X1)
% 2.16/1.01      | k1_yellow_0(X0,k2_relat_1(X1)) = k4_yellow_2(X0,X1) ),
% 2.16/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_669,plain,
% 2.16/1.01      ( ~ v2_struct_0(X0) | ~ l1_orders_2(X0) | sK3 != X0 ),
% 2.16/1.01      inference(resolution_lifted,[status(thm)],[c_5,c_33]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_670,plain,
% 2.16/1.01      ( ~ v2_struct_0(sK3) | ~ l1_orders_2(sK3) ),
% 2.16/1.01      inference(unflattening,[status(thm)],[c_669]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_672,plain,
% 2.16/1.01      ( ~ v2_struct_0(sK3) ),
% 2.16/1.01      inference(global_propositional_subsumption,
% 2.16/1.01                [status(thm)],
% 2.16/1.01                [c_670,c_33,c_31,c_72,c_108]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_855,plain,
% 2.16/1.01      ( ~ l1_orders_2(X0)
% 2.16/1.01      | ~ v1_relat_1(X1)
% 2.16/1.01      | k1_yellow_0(X0,k2_relat_1(X1)) = k4_yellow_2(X0,X1)
% 2.16/1.01      | sK3 != X0 ),
% 2.16/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_672]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_856,plain,
% 2.16/1.01      ( ~ l1_orders_2(sK3)
% 2.16/1.01      | ~ v1_relat_1(X0)
% 2.16/1.01      | k1_yellow_0(sK3,k2_relat_1(X0)) = k4_yellow_2(sK3,X0) ),
% 2.16/1.01      inference(unflattening,[status(thm)],[c_855]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_860,plain,
% 2.16/1.01      ( ~ v1_relat_1(X0)
% 2.16/1.01      | k1_yellow_0(sK3,k2_relat_1(X0)) = k4_yellow_2(sK3,X0) ),
% 2.16/1.01      inference(global_propositional_subsumption,
% 2.16/1.01                [status(thm)],
% 2.16/1.01                [c_856,c_31,c_72]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_2231,plain,
% 2.16/1.01      ( ~ v1_relat_1(X0_67)
% 2.16/1.01      | k1_yellow_0(sK3,k2_relat_1(X0_67)) = k4_yellow_2(sK3,X0_67) ),
% 2.16/1.01      inference(subtyping,[status(esa)],[c_860]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_2669,plain,
% 2.16/1.01      ( k1_yellow_0(sK3,k2_relat_1(X0_67)) = k4_yellow_2(sK3,X0_67)
% 2.16/1.01      | v1_relat_1(X0_67) != iProver_top ),
% 2.16/1.01      inference(predicate_to_equality,[status(thm)],[c_2231]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_3190,plain,
% 2.16/1.01      ( k1_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = k4_yellow_2(sK3,u1_waybel_0(sK3,sK5)) ),
% 2.16/1.01      inference(superposition,[status(thm)],[c_2922,c_2669]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_15,plain,
% 2.16/1.01      ( ~ l1_waybel_0(X0,X1)
% 2.16/1.01      | v2_struct_0(X1)
% 2.16/1.01      | ~ l1_orders_2(X1)
% 2.16/1.01      | k4_yellow_2(X1,u1_waybel_0(X1,X0)) = k1_waybel_2(X1,X0) ),
% 2.16/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_829,plain,
% 2.16/1.01      ( v2_struct_0(X0)
% 2.16/1.01      | ~ l1_orders_2(X0)
% 2.16/1.01      | k4_yellow_2(X0,u1_waybel_0(X0,X1)) = k1_waybel_2(X0,X1)
% 2.16/1.01      | sK5 != X1
% 2.16/1.01      | sK3 != X0 ),
% 2.16/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_26]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_830,plain,
% 2.16/1.01      ( v2_struct_0(sK3)
% 2.16/1.01      | ~ l1_orders_2(sK3)
% 2.16/1.01      | k4_yellow_2(sK3,u1_waybel_0(sK3,sK5)) = k1_waybel_2(sK3,sK5) ),
% 2.16/1.01      inference(unflattening,[status(thm)],[c_829]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_832,plain,
% 2.16/1.01      ( k4_yellow_2(sK3,u1_waybel_0(sK3,sK5)) = k1_waybel_2(sK3,sK5) ),
% 2.16/1.01      inference(global_propositional_subsumption,
% 2.16/1.01                [status(thm)],
% 2.16/1.01                [c_830,c_33,c_31,c_72,c_108]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_2232,plain,
% 2.16/1.01      ( k4_yellow_2(sK3,u1_waybel_0(sK3,sK5)) = k1_waybel_2(sK3,sK5) ),
% 2.16/1.01      inference(subtyping,[status(esa)],[c_832]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_3191,plain,
% 2.16/1.01      ( k1_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = k1_waybel_2(sK3,sK5) ),
% 2.16/1.01      inference(light_normalisation,[status(thm)],[c_3190,c_2232]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_3541,plain,
% 2.16/1.01      ( k1_waybel_2(sK3,sK5) = X0_67
% 2.16/1.01      | r2_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_67) != iProver_top
% 2.16/1.01      | r1_orders_2(sK3,sK4,sK0(sK3,X0_67,k2_relat_1(u1_waybel_0(sK3,sK5)))) = iProver_top
% 2.16/1.01      | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top
% 2.16/1.01      | m1_subset_1(sK0(sK3,X0_67,k2_relat_1(u1_waybel_0(sK3,sK5))),u1_struct_0(sK3)) != iProver_top ),
% 2.16/1.01      inference(demodulation,[status(thm)],[c_3523,c_3191]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_3791,plain,
% 2.16/1.01      ( k1_waybel_2(sK3,sK5) = X0_67
% 2.16/1.01      | k1_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = X0_67
% 2.16/1.01      | r2_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_67) != iProver_top
% 2.16/1.01      | r1_orders_2(sK3,sK4,sK0(sK3,X0_67,k2_relat_1(u1_waybel_0(sK3,sK5)))) = iProver_top
% 2.16/1.01      | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top ),
% 2.16/1.01      inference(superposition,[status(thm)],[c_2678,c_3541]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_3797,plain,
% 2.16/1.01      ( k1_waybel_2(sK3,sK5) = X0_67
% 2.16/1.01      | r2_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_67) != iProver_top
% 2.16/1.01      | r1_orders_2(sK3,sK4,sK0(sK3,X0_67,k2_relat_1(u1_waybel_0(sK3,sK5)))) = iProver_top
% 2.16/1.01      | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top ),
% 2.16/1.01      inference(demodulation,[status(thm)],[c_3791,c_3191]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_9,plain,
% 2.16/1.01      ( ~ r2_lattice3(X0,X1,X2)
% 2.16/1.01      | ~ r1_orders_2(X0,X2,sK0(X0,X2,X1))
% 2.16/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.16/1.01      | ~ v5_orders_2(X0)
% 2.16/1.01      | ~ l1_orders_2(X0)
% 2.16/1.01      | k1_yellow_0(X0,X1) = X2 ),
% 2.16/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_1173,plain,
% 2.16/1.01      ( ~ r2_lattice3(X0,X1,X2)
% 2.16/1.01      | ~ r1_orders_2(X0,X2,sK0(X0,X2,X1))
% 2.16/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.16/1.01      | ~ l1_orders_2(X0)
% 2.16/1.01      | k1_yellow_0(X0,X1) = X2
% 2.16/1.01      | sK3 != X0 ),
% 2.16/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_35]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_1174,plain,
% 2.16/1.01      ( ~ r2_lattice3(sK3,X0,X1)
% 2.16/1.01      | ~ r1_orders_2(sK3,X1,sK0(sK3,X1,X0))
% 2.16/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.16/1.01      | ~ l1_orders_2(sK3)
% 2.16/1.01      | k1_yellow_0(sK3,X0) = X1 ),
% 2.16/1.01      inference(unflattening,[status(thm)],[c_1173]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_1178,plain,
% 2.16/1.01      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.16/1.01      | ~ r1_orders_2(sK3,X1,sK0(sK3,X1,X0))
% 2.16/1.01      | ~ r2_lattice3(sK3,X0,X1)
% 2.16/1.01      | k1_yellow_0(sK3,X0) = X1 ),
% 2.16/1.01      inference(global_propositional_subsumption,
% 2.16/1.01                [status(thm)],
% 2.16/1.01                [c_1174,c_31,c_72]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_1179,plain,
% 2.16/1.01      ( ~ r2_lattice3(sK3,X0,X1)
% 2.16/1.01      | ~ r1_orders_2(sK3,X1,sK0(sK3,X1,X0))
% 2.16/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.16/1.01      | k1_yellow_0(sK3,X0) = X1 ),
% 2.16/1.01      inference(renaming,[status(thm)],[c_1178]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_2222,plain,
% 2.16/1.01      ( ~ r2_lattice3(sK3,X0_69,X0_67)
% 2.16/1.01      | ~ r1_orders_2(sK3,X0_67,sK0(sK3,X0_67,X0_69))
% 2.16/1.01      | ~ m1_subset_1(X0_67,u1_struct_0(sK3))
% 2.16/1.01      | k1_yellow_0(sK3,X0_69) = X0_67 ),
% 2.16/1.01      inference(subtyping,[status(esa)],[c_1179]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_2680,plain,
% 2.16/1.01      ( k1_yellow_0(sK3,X0_69) = X0_67
% 2.16/1.01      | r2_lattice3(sK3,X0_69,X0_67) != iProver_top
% 2.16/1.01      | r1_orders_2(sK3,X0_67,sK0(sK3,X0_67,X0_69)) != iProver_top
% 2.16/1.01      | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top ),
% 2.16/1.01      inference(predicate_to_equality,[status(thm)],[c_2222]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_3811,plain,
% 2.16/1.01      ( k1_waybel_2(sK3,sK5) = sK4
% 2.16/1.01      | k1_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = sK4
% 2.16/1.01      | r2_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),sK4) != iProver_top
% 2.16/1.01      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 2.16/1.01      inference(superposition,[status(thm)],[c_3797,c_2680]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_3816,plain,
% 2.16/1.01      ( k1_waybel_2(sK3,sK5) = sK4
% 2.16/1.01      | r2_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),sK4) != iProver_top
% 2.16/1.01      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 2.16/1.01      inference(demodulation,[status(thm)],[c_3811,c_3191]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_18,plain,
% 2.16/1.01      ( ~ v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0)
% 2.16/1.01      | ~ r3_waybel_9(X0,X1,X2)
% 2.16/1.01      | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
% 2.16/1.01      | ~ v10_waybel_0(X1,X0)
% 2.16/1.01      | ~ l1_waybel_0(X1,X0)
% 2.16/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.16/1.01      | ~ v2_pre_topc(X0)
% 2.16/1.01      | ~ v8_pre_topc(X0)
% 2.16/1.01      | ~ v1_lattice3(X0)
% 2.16/1.01      | ~ v1_compts_1(X0)
% 2.16/1.01      | ~ v4_orders_2(X1)
% 2.16/1.01      | ~ v4_orders_2(X0)
% 2.16/1.01      | ~ v7_waybel_0(X1)
% 2.16/1.01      | ~ l1_waybel_9(X0)
% 2.16/1.01      | ~ v5_orders_2(X0)
% 2.16/1.01      | ~ v2_lattice3(X0)
% 2.16/1.01      | v2_struct_0(X1)
% 2.16/1.01      | ~ v3_orders_2(X0) ),
% 2.16/1.01      inference(cnf_transformation,[],[f96]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_24,negated_conjecture,
% 2.16/1.01      ( v10_waybel_0(sK5,sK3) ),
% 2.16/1.01      inference(cnf_transformation,[],[f91]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_497,plain,
% 2.16/1.01      ( ~ v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0)
% 2.16/1.01      | ~ r3_waybel_9(X0,X1,X2)
% 2.16/1.01      | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
% 2.16/1.01      | ~ l1_waybel_0(X1,X0)
% 2.16/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.16/1.01      | ~ v2_pre_topc(X0)
% 2.16/1.01      | ~ v8_pre_topc(X0)
% 2.16/1.01      | ~ v1_lattice3(X0)
% 2.16/1.01      | ~ v1_compts_1(X0)
% 2.16/1.01      | ~ v4_orders_2(X1)
% 2.16/1.01      | ~ v4_orders_2(X0)
% 2.16/1.01      | ~ v7_waybel_0(X1)
% 2.16/1.01      | ~ l1_waybel_9(X0)
% 2.16/1.01      | ~ v5_orders_2(X0)
% 2.16/1.01      | ~ v2_lattice3(X0)
% 2.16/1.01      | v2_struct_0(X1)
% 2.16/1.01      | ~ v3_orders_2(X0)
% 2.16/1.01      | sK5 != X1
% 2.16/1.01      | sK3 != X0 ),
% 2.16/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_24]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_498,plain,
% 2.16/1.01      ( ~ v5_pre_topc(k4_waybel_1(sK3,sK1(sK3)),sK3,sK3)
% 2.16/1.01      | ~ r3_waybel_9(sK3,sK5,X0)
% 2.16/1.01      | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 2.16/1.01      | ~ l1_waybel_0(sK5,sK3)
% 2.16/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.16/1.01      | ~ v2_pre_topc(sK3)
% 2.16/1.01      | ~ v8_pre_topc(sK3)
% 2.16/1.01      | ~ v1_lattice3(sK3)
% 2.16/1.01      | ~ v1_compts_1(sK3)
% 2.16/1.01      | ~ v4_orders_2(sK5)
% 2.16/1.01      | ~ v4_orders_2(sK3)
% 2.16/1.01      | ~ v7_waybel_0(sK5)
% 2.16/1.01      | ~ l1_waybel_9(sK3)
% 2.16/1.01      | ~ v5_orders_2(sK3)
% 2.16/1.01      | ~ v2_lattice3(sK3)
% 2.16/1.01      | v2_struct_0(sK5)
% 2.16/1.01      | ~ v3_orders_2(sK3) ),
% 2.16/1.01      inference(unflattening,[status(thm)],[c_497]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_502,plain,
% 2.16/1.01      ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 2.16/1.01      | ~ r3_waybel_9(sK3,sK5,X0)
% 2.16/1.01      | ~ v5_pre_topc(k4_waybel_1(sK3,sK1(sK3)),sK3,sK3)
% 2.16/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 2.16/1.01      inference(global_propositional_subsumption,
% 2.16/1.01                [status(thm)],
% 2.16/1.01                [c_498,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_31,c_29,
% 2.16/1.01                 c_28,c_27,c_26]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_503,plain,
% 2.16/1.01      ( ~ v5_pre_topc(k4_waybel_1(sK3,sK1(sK3)),sK3,sK3)
% 2.16/1.01      | ~ r3_waybel_9(sK3,sK5,X0)
% 2.16/1.01      | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 2.16/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 2.16/1.01      inference(renaming,[status(thm)],[c_502]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_576,plain,
% 2.16/1.01      ( ~ r3_waybel_9(sK3,sK5,X0)
% 2.16/1.01      | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 2.16/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.16/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.16/1.01      | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X1)
% 2.16/1.01      | sK3 != sK3 ),
% 2.16/1.01      inference(resolution_lifted,[status(thm)],[c_25,c_503]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_961,plain,
% 2.16/1.01      ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 2.16/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.16/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.16/1.01      | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X1)
% 2.16/1.01      | sK4 != X0
% 2.16/1.01      | sK5 != sK5
% 2.16/1.01      | sK3 != sK3 ),
% 2.16/1.01      inference(resolution_lifted,[status(thm)],[c_23,c_576]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_962,plain,
% 2.16/1.01      ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
% 2.16/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.16/1.01      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 2.16/1.01      | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0) ),
% 2.16/1.01      inference(unflattening,[status(thm)],[c_961]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_966,plain,
% 2.16/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.16/1.01      | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
% 2.16/1.01      | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0) ),
% 2.16/1.01      inference(global_propositional_subsumption,
% 2.16/1.01                [status(thm)],
% 2.16/1.01                [c_962,c_30]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_967,plain,
% 2.16/1.01      ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
% 2.16/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.16/1.01      | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0) ),
% 2.16/1.01      inference(renaming,[status(thm)],[c_966]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_2230,plain,
% 2.16/1.01      ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
% 2.16/1.01      | ~ m1_subset_1(X0_67,u1_struct_0(sK3))
% 2.16/1.01      | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0_67) ),
% 2.16/1.01      inference(subtyping,[status(esa)],[c_967]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_2670,plain,
% 2.16/1.01      ( k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0_67)
% 2.16/1.01      | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) = iProver_top
% 2.16/1.01      | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top ),
% 2.16/1.01      inference(predicate_to_equality,[status(thm)],[c_2230]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_19,plain,
% 2.16/1.01      ( ~ r3_waybel_9(X0,X1,X2)
% 2.16/1.01      | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
% 2.16/1.01      | ~ v10_waybel_0(X1,X0)
% 2.16/1.01      | ~ l1_waybel_0(X1,X0)
% 2.16/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.16/1.01      | m1_subset_1(sK1(X0),u1_struct_0(X0))
% 2.16/1.01      | ~ v2_pre_topc(X0)
% 2.16/1.01      | ~ v8_pre_topc(X0)
% 2.16/1.01      | ~ v1_lattice3(X0)
% 2.16/1.01      | ~ v1_compts_1(X0)
% 2.16/1.01      | ~ v4_orders_2(X1)
% 2.16/1.01      | ~ v4_orders_2(X0)
% 2.16/1.01      | ~ v7_waybel_0(X1)
% 2.16/1.01      | ~ l1_waybel_9(X0)
% 2.16/1.01      | ~ v5_orders_2(X0)
% 2.16/1.01      | ~ v2_lattice3(X0)
% 2.16/1.01      | v2_struct_0(X1)
% 2.16/1.01      | ~ v3_orders_2(X0) ),
% 2.16/1.01      inference(cnf_transformation,[],[f97]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_473,plain,
% 2.16/1.01      ( ~ r3_waybel_9(X0,X1,X2)
% 2.16/1.01      | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
% 2.16/1.01      | ~ l1_waybel_0(X1,X0)
% 2.16/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.16/1.01      | m1_subset_1(sK1(X0),u1_struct_0(X0))
% 2.16/1.01      | ~ v2_pre_topc(X0)
% 2.16/1.01      | ~ v8_pre_topc(X0)
% 2.16/1.01      | ~ v1_lattice3(X0)
% 2.16/1.01      | ~ v1_compts_1(X0)
% 2.16/1.01      | ~ v4_orders_2(X1)
% 2.16/1.01      | ~ v4_orders_2(X0)
% 2.16/1.01      | ~ v7_waybel_0(X1)
% 2.16/1.01      | ~ l1_waybel_9(X0)
% 2.16/1.01      | ~ v5_orders_2(X0)
% 2.16/1.01      | ~ v2_lattice3(X0)
% 2.16/1.01      | v2_struct_0(X1)
% 2.16/1.01      | ~ v3_orders_2(X0)
% 2.16/1.01      | sK5 != X1
% 2.16/1.01      | sK3 != X0 ),
% 2.16/1.01      inference(resolution_lifted,[status(thm)],[c_19,c_24]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_474,plain,
% 2.16/1.01      ( ~ r3_waybel_9(sK3,sK5,X0)
% 2.16/1.01      | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 2.16/1.01      | ~ l1_waybel_0(sK5,sK3)
% 2.16/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.16/1.01      | m1_subset_1(sK1(sK3),u1_struct_0(sK3))
% 2.16/1.01      | ~ v2_pre_topc(sK3)
% 2.16/1.01      | ~ v8_pre_topc(sK3)
% 2.16/1.01      | ~ v1_lattice3(sK3)
% 2.16/1.01      | ~ v1_compts_1(sK3)
% 2.16/1.01      | ~ v4_orders_2(sK5)
% 2.16/1.01      | ~ v4_orders_2(sK3)
% 2.16/1.01      | ~ v7_waybel_0(sK5)
% 2.16/1.01      | ~ l1_waybel_9(sK3)
% 2.16/1.01      | ~ v5_orders_2(sK3)
% 2.16/1.01      | ~ v2_lattice3(sK3)
% 2.16/1.01      | v2_struct_0(sK5)
% 2.16/1.01      | ~ v3_orders_2(sK3) ),
% 2.16/1.01      inference(unflattening,[status(thm)],[c_473]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_478,plain,
% 2.16/1.01      ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 2.16/1.01      | ~ r3_waybel_9(sK3,sK5,X0)
% 2.16/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.16/1.01      | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) ),
% 2.16/1.01      inference(global_propositional_subsumption,
% 2.16/1.01                [status(thm)],
% 2.16/1.01                [c_474,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_31,c_29,
% 2.16/1.01                 c_28,c_27,c_26]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_479,plain,
% 2.16/1.01      ( ~ r3_waybel_9(sK3,sK5,X0)
% 2.16/1.01      | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 2.16/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.16/1.01      | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) ),
% 2.16/1.01      inference(renaming,[status(thm)],[c_478]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_982,plain,
% 2.16/1.01      ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 2.16/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.16/1.01      | m1_subset_1(sK1(sK3),u1_struct_0(sK3))
% 2.16/1.01      | sK4 != X0
% 2.16/1.01      | sK5 != sK5
% 2.16/1.01      | sK3 != sK3 ),
% 2.16/1.01      inference(resolution_lifted,[status(thm)],[c_23,c_479]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_983,plain,
% 2.16/1.01      ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
% 2.16/1.01      | m1_subset_1(sK1(sK3),u1_struct_0(sK3))
% 2.16/1.01      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 2.16/1.01      inference(unflattening,[status(thm)],[c_982]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_985,plain,
% 2.16/1.01      ( m1_subset_1(sK1(sK3),u1_struct_0(sK3))
% 2.16/1.01      | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) ),
% 2.16/1.01      inference(global_propositional_subsumption,
% 2.16/1.01                [status(thm)],
% 2.16/1.01                [c_983,c_30]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_986,plain,
% 2.16/1.01      ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
% 2.16/1.01      | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) ),
% 2.16/1.01      inference(renaming,[status(thm)],[c_985]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_987,plain,
% 2.16/1.01      ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) = iProver_top
% 2.16/1.01      | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) = iProver_top ),
% 2.16/1.01      inference(predicate_to_equality,[status(thm)],[c_986]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_2246,plain,( X0_71 = X0_71 ),theory(equality) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_2861,plain,
% 2.16/1.01      ( k4_waybel_1(sK3,sK1(sK3)) = k4_waybel_1(sK3,sK1(sK3)) ),
% 2.16/1.01      inference(instantiation,[status(thm)],[c_2246]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_2862,plain,
% 2.16/1.01      ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
% 2.16/1.01      | ~ m1_subset_1(sK1(sK3),u1_struct_0(sK3))
% 2.16/1.01      | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,sK1(sK3)) ),
% 2.16/1.01      inference(instantiation,[status(thm)],[c_2230]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_2863,plain,
% 2.16/1.01      ( k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,sK1(sK3))
% 2.16/1.01      | r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) = iProver_top
% 2.16/1.01      | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) != iProver_top ),
% 2.16/1.01      inference(predicate_to_equality,[status(thm)],[c_2862]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_2873,plain,
% 2.16/1.01      ( r2_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) = iProver_top ),
% 2.16/1.01      inference(global_propositional_subsumption,
% 2.16/1.01                [status(thm)],
% 2.16/1.01                [c_2670,c_987,c_2861,c_2863]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_2979,plain,
% 2.16/1.01      ( r2_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),sK4) = iProver_top ),
% 2.16/1.01      inference(demodulation,[status(thm)],[c_2927,c_2873]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_22,negated_conjecture,
% 2.16/1.01      ( k1_waybel_2(sK3,sK5) != sK4 ),
% 2.16/1.01      inference(cnf_transformation,[],[f93]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_2235,negated_conjecture,
% 2.16/1.01      ( k1_waybel_2(sK3,sK5) != sK4 ),
% 2.16/1.01      inference(subtyping,[status(esa)],[c_22]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(c_49,plain,
% 2.16/1.01      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 2.16/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.16/1.01  
% 2.16/1.01  cnf(contradiction,plain,
% 2.16/1.01      ( $false ),
% 2.16/1.01      inference(minisat,[status(thm)],[c_3816,c_2979,c_2235,c_49]) ).
% 2.16/1.01  
% 2.16/1.01  
% 2.16/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.16/1.01  
% 2.16/1.01  ------                               Statistics
% 2.16/1.01  
% 2.16/1.01  ------ General
% 2.16/1.01  
% 2.16/1.01  abstr_ref_over_cycles:                  0
% 2.16/1.01  abstr_ref_under_cycles:                 0
% 2.16/1.01  gc_basic_clause_elim:                   0
% 2.16/1.01  forced_gc_time:                         0
% 2.16/1.01  parsing_time:                           0.011
% 2.16/1.01  unif_index_cands_time:                  0.
% 2.16/1.01  unif_index_add_time:                    0.
% 2.16/1.01  orderings_time:                         0.
% 2.16/1.01  out_proof_time:                         0.027
% 2.16/1.01  total_time:                             0.18
% 2.16/1.01  num_of_symbols:                         75
% 2.16/1.01  num_of_terms:                           2454
% 2.16/1.01  
% 2.16/1.01  ------ Preprocessing
% 2.16/1.01  
% 2.16/1.01  num_of_splits:                          2
% 2.16/1.01  num_of_split_atoms:                     2
% 2.16/1.01  num_of_reused_defs:                     0
% 2.16/1.01  num_eq_ax_congr_red:                    30
% 2.16/1.01  num_of_sem_filtered_clauses:            1
% 2.16/1.01  num_of_subtypes:                        6
% 2.16/1.01  monotx_restored_types:                  0
% 2.16/1.01  sat_num_of_epr_types:                   0
% 2.16/1.01  sat_num_of_non_cyclic_types:            0
% 2.16/1.01  sat_guarded_non_collapsed_types:        1
% 2.16/1.01  num_pure_diseq_elim:                    0
% 2.16/1.01  simp_replaced_by:                       0
% 2.16/1.01  res_preprocessed:                       157
% 2.16/1.01  prep_upred:                             0
% 2.16/1.01  prep_unflattend:                        60
% 2.16/1.01  smt_new_axioms:                         0
% 2.16/1.01  pred_elim_cands:                        5
% 2.16/1.01  pred_elim:                              18
% 2.16/1.01  pred_elim_cl:                           20
% 2.16/1.01  pred_elim_cycles:                       26
% 2.16/1.01  merged_defs:                            0
% 2.16/1.01  merged_defs_ncl:                        0
% 2.16/1.01  bin_hyper_res:                          0
% 2.16/1.01  prep_cycles:                            4
% 2.16/1.01  pred_elim_time:                         0.035
% 2.16/1.01  splitting_time:                         0.
% 2.16/1.01  sem_filter_time:                        0.
% 2.16/1.01  monotx_time:                            0.
% 2.16/1.01  subtype_inf_time:                       0.
% 2.16/1.01  
% 2.16/1.01  ------ Problem properties
% 2.16/1.01  
% 2.16/1.01  clauses:                                22
% 2.16/1.01  conjectures:                            2
% 2.16/1.01  epr:                                    1
% 2.16/1.01  horn:                                   15
% 2.16/1.01  ground:                                 6
% 2.16/1.01  unary:                                  4
% 2.16/1.01  binary:                                 5
% 2.16/1.01  lits:                                   63
% 2.16/1.01  lits_eq:                                11
% 2.16/1.01  fd_pure:                                0
% 2.16/1.01  fd_pseudo:                              0
% 2.16/1.01  fd_cond:                                0
% 2.16/1.01  fd_pseudo_cond:                         3
% 2.16/1.01  ac_symbols:                             0
% 2.16/1.01  
% 2.16/1.01  ------ Propositional Solver
% 2.16/1.01  
% 2.16/1.01  prop_solver_calls:                      26
% 2.16/1.01  prop_fast_solver_calls:                 1638
% 2.16/1.01  smt_solver_calls:                       0
% 2.16/1.01  smt_fast_solver_calls:                  0
% 2.16/1.01  prop_num_of_clauses:                    892
% 2.16/1.01  prop_preprocess_simplified:             4689
% 2.16/1.01  prop_fo_subsumed:                       88
% 2.16/1.01  prop_solver_time:                       0.
% 2.16/1.01  smt_solver_time:                        0.
% 2.16/1.01  smt_fast_solver_time:                   0.
% 2.16/1.01  prop_fast_solver_time:                  0.
% 2.16/1.01  prop_unsat_core_time:                   0.
% 2.16/1.01  
% 2.16/1.01  ------ QBF
% 2.16/1.01  
% 2.16/1.01  qbf_q_res:                              0
% 2.16/1.01  qbf_num_tautologies:                    0
% 2.16/1.01  qbf_prep_cycles:                        0
% 2.16/1.01  
% 2.16/1.01  ------ BMC1
% 2.16/1.01  
% 2.16/1.01  bmc1_current_bound:                     -1
% 2.16/1.01  bmc1_last_solved_bound:                 -1
% 2.16/1.01  bmc1_unsat_core_size:                   -1
% 2.16/1.01  bmc1_unsat_core_parents_size:           -1
% 2.16/1.01  bmc1_merge_next_fun:                    0
% 2.16/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.16/1.01  
% 2.16/1.01  ------ Instantiation
% 2.16/1.01  
% 2.16/1.01  inst_num_of_clauses:                    208
% 2.16/1.01  inst_num_in_passive:                    52
% 2.16/1.01  inst_num_in_active:                     147
% 2.16/1.01  inst_num_in_unprocessed:                9
% 2.16/1.01  inst_num_of_loops:                      160
% 2.16/1.01  inst_num_of_learning_restarts:          0
% 2.16/1.01  inst_num_moves_active_passive:          10
% 2.16/1.01  inst_lit_activity:                      0
% 2.16/1.01  inst_lit_activity_moves:                0
% 2.16/1.01  inst_num_tautologies:                   0
% 2.16/1.01  inst_num_prop_implied:                  0
% 2.16/1.01  inst_num_existing_simplified:           0
% 2.16/1.01  inst_num_eq_res_simplified:             0
% 2.16/1.01  inst_num_child_elim:                    0
% 2.16/1.01  inst_num_of_dismatching_blockings:      18
% 2.16/1.01  inst_num_of_non_proper_insts:           152
% 2.16/1.01  inst_num_of_duplicates:                 0
% 2.16/1.01  inst_inst_num_from_inst_to_res:         0
% 2.16/1.01  inst_dismatching_checking_time:         0.
% 2.16/1.01  
% 2.16/1.01  ------ Resolution
% 2.16/1.01  
% 2.16/1.01  res_num_of_clauses:                     0
% 2.16/1.01  res_num_in_passive:                     0
% 2.16/1.01  res_num_in_active:                      0
% 2.16/1.01  res_num_of_loops:                       161
% 2.16/1.01  res_forward_subset_subsumed:            34
% 2.16/1.01  res_backward_subset_subsumed:           0
% 2.16/1.01  res_forward_subsumed:                   0
% 2.16/1.01  res_backward_subsumed:                  0
% 2.16/1.01  res_forward_subsumption_resolution:     2
% 2.16/1.01  res_backward_subsumption_resolution:    0
% 2.16/1.01  res_clause_to_clause_subsumption:       172
% 2.16/1.01  res_orphan_elimination:                 0
% 2.16/1.01  res_tautology_del:                      20
% 2.16/1.01  res_num_eq_res_simplified:              0
% 2.16/1.01  res_num_sel_changes:                    0
% 2.16/1.01  res_moves_from_active_to_pass:          0
% 2.16/1.01  
% 2.16/1.01  ------ Superposition
% 2.16/1.01  
% 2.16/1.01  sup_time_total:                         0.
% 2.16/1.01  sup_time_generating:                    0.
% 2.16/1.01  sup_time_sim_full:                      0.
% 2.16/1.01  sup_time_sim_immed:                     0.
% 2.16/1.01  
% 2.16/1.01  sup_num_of_clauses:                     37
% 2.16/1.01  sup_num_in_active:                      29
% 2.16/1.01  sup_num_in_passive:                     8
% 2.16/1.01  sup_num_of_loops:                       31
% 2.16/1.01  sup_fw_superposition:                   16
% 2.16/1.01  sup_bw_superposition:                   7
% 2.16/1.01  sup_immediate_simplified:               13
% 2.16/1.01  sup_given_eliminated:                   0
% 2.16/1.01  comparisons_done:                       0
% 2.16/1.01  comparisons_avoided:                    0
% 2.16/1.01  
% 2.16/1.01  ------ Simplifications
% 2.16/1.01  
% 2.16/1.01  
% 2.16/1.01  sim_fw_subset_subsumed:                 0
% 2.16/1.01  sim_bw_subset_subsumed:                 6
% 2.16/1.01  sim_fw_subsumed:                        2
% 2.16/1.01  sim_bw_subsumed:                        1
% 2.16/1.01  sim_fw_subsumption_res:                 1
% 2.16/1.01  sim_bw_subsumption_res:                 0
% 2.16/1.01  sim_tautology_del:                      1
% 2.16/1.01  sim_eq_tautology_del:                   0
% 2.16/1.01  sim_eq_res_simp:                        0
% 2.16/1.01  sim_fw_demodulated:                     6
% 2.16/1.01  sim_bw_demodulated:                     1
% 2.16/1.01  sim_light_normalised:                   5
% 2.16/1.01  sim_joinable_taut:                      0
% 2.16/1.01  sim_joinable_simp:                      0
% 2.16/1.01  sim_ac_normalised:                      0
% 2.16/1.01  sim_smt_subsumption:                    0
% 2.16/1.01  
%------------------------------------------------------------------------------
