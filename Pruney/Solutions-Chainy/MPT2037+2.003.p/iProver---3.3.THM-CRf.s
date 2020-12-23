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
% DateTime   : Thu Dec  3 12:28:59 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :  239 (2269 expanded)
%              Number of clauses        :  153 ( 482 expanded)
%              Number of leaves         :   19 ( 742 expanded)
%              Depth                    :   34
%              Number of atoms          : 1490 (32650 expanded)
%              Number of equality atoms :  224 (2265 expanded)
%              Maximal formula depth    :   27 (   7 average)
%              Maximal clause size      :   38 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) )
               => ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 ) )
              & ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) )
               => ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 ) )
              & ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X4,X1) ) )
                  & r1_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f5])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X1)
          & r1_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X1)
        & r1_lattice3(X0,X2,sK0(X0,X1,X2))
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X1)
                  & r1_lattice3(X0,X2,sK0(X0,X1,X2))
                  & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f39])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X2) = X1
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
                    & v11_waybel_0(X2,X0)
                    & ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) ) )
                 => k1_waybel_9(X0,X2) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_waybel_9(X0,X2) != X1
              & r3_waybel_9(X0,X2,X1)
              & v11_waybel_0(X2,X0)
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
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_waybel_9(X0,X2) != X1
              & r3_waybel_9(X0,X2,X1)
              & v11_waybel_0(X2,X0)
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
    inference(flattening,[],[f37])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k1_waybel_9(X0,X2) != X1
          & r3_waybel_9(X0,X2,X1)
          & v11_waybel_0(X2,X0)
          & ! [X3] :
              ( v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & l1_waybel_0(X2,X0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
     => ( k1_waybel_9(X0,sK5) != X1
        & r3_waybel_9(X0,sK5,X1)
        & v11_waybel_0(sK5,X0)
        & ! [X3] :
            ( v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & l1_waybel_0(sK5,X0)
        & v7_waybel_0(sK5)
        & v4_orders_2(sK5)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_waybel_9(X0,X2) != X1
              & r3_waybel_9(X0,X2,X1)
              & v11_waybel_0(X2,X0)
              & ! [X3] :
                  ( v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & l1_waybel_0(X2,X0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_waybel_9(X0,X2) != sK4
            & r3_waybel_9(X0,X2,sK4)
            & v11_waybel_0(X2,X0)
            & ! [X3] :
                ( v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_waybel_9(X0,X2) != X1
                & r3_waybel_9(X0,X2,X1)
                & v11_waybel_0(X2,X0)
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
              ( k1_waybel_9(sK3,X2) != X1
              & r3_waybel_9(sK3,X2,X1)
              & v11_waybel_0(X2,sK3)
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

fof(f49,plain,
    ( k1_waybel_9(sK3,sK5) != sK4
    & r3_waybel_9(sK3,sK5,sK4)
    & v11_waybel_0(sK5,sK3)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f38,f48,f47,f46])).

fof(f74,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f78,plain,(
    l1_waybel_9(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => ( l1_orders_2(X0)
        & l1_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => l1_orders_2(X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f32,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f65,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X2) = X1
      | r1_lattice3(X0,X2,sK0(X0,X1,X2))
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f86,plain,(
    r3_waybel_9(sK3,sK5,sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f82,plain,(
    v7_waybel_0(sK5) ),
    inference(cnf_transformation,[],[f49])).

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
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) )
                      & X2 = X3 )
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
                         => r1_orders_2(X0,X4,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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
    inference(rectify,[],[f11])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

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
    inference(rectify,[],[f36])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X5] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X5),X0,X0)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0)
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r1_orders_2(X0,X4,X3)
                      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_orders_2(X0,X4,X3)
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
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
    inference(cnf_transformation,[],[f45])).

fof(f92,plain,(
    ! [X4,X0,X3,X1] :
      ( r1_orders_2(X0,X4,X3)
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
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
    inference(equality_resolution,[],[f69])).

fof(f84,plain,(
    ! [X3] :
      ( v5_pre_topc(k4_waybel_1(sK3,X3),sK3,sK3)
      | ~ m1_subset_1(X3,u1_struct_0(sK3)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f70,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f71,plain,(
    v8_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f72,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f73,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f75,plain,(
    v1_lattice3(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f76,plain,(
    v2_lattice3(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f77,plain,(
    v1_compts_1(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f80,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f81,plain,(
    v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f83,plain,(
    l1_waybel_0(sK5,sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f79,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f49])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_orders_2(X0,X4,X3)
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
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
    inference(cnf_transformation,[],[f45])).

fof(f93,plain,(
    ! [X4,X0,X3,X1] :
      ( r1_orders_2(X0,X4,X3)
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
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
    inference(equality_resolution,[],[f68])).

fof(f6,axiom,(
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
    inference(pure_predicate_removal,[],[f6])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
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

fof(f51,plain,(
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

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_yellow_0(X0,k2_relat_1(X1)) = k5_yellow_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow_0(X0,k2_relat_1(X1)) = k5_yellow_2(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow_0(X0,k2_relat_1(X1)) = k5_yellow_2(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_yellow_0(X0,k2_relat_1(X1)) = k5_yellow_2(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1))
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1))
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X2) = X1
      | ~ r1_orders_2(X0,sK0(X0,X1,X2),X1)
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

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

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X4] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0)
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v11_waybel_0(X1,X0)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f41])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v11_waybel_0(X1,X0)
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
    inference(cnf_transformation,[],[f42])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v11_waybel_0(X1,X0)
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
    inference(equality_resolution,[],[f67])).

fof(f85,plain,(
    v11_waybel_0(sK5,sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v11_waybel_0(X1,X0)
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
    inference(cnf_transformation,[],[f42])).

fof(f91,plain,(
    ! [X0,X3,X1] :
      ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v11_waybel_0(X1,X0)
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
    inference(equality_resolution,[],[f66])).

fof(f87,plain,(
    k1_waybel_9(sK3,sK5) != sK4 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_9,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_33,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_982,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X2,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_33])).

cnf(c_983,plain,
    ( ~ r1_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK0(sK3,X1,X0),u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | k2_yellow_0(sK3,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_982])).

cnf(c_29,negated_conjecture,
    ( l1_waybel_9(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_15,plain,
    ( ~ l1_waybel_9(X0)
    | l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_70,plain,
    ( ~ l1_waybel_9(sK3)
    | l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_987,plain,
    ( m1_subset_1(sK0(sK3,X1,X0),u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r1_lattice3(sK3,X0,X1)
    | k2_yellow_0(sK3,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_983,c_29,c_70])).

cnf(c_988,plain,
    ( ~ r1_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK0(sK3,X1,X0),u1_struct_0(sK3))
    | k2_yellow_0(sK3,X0) = X1 ),
    inference(renaming,[status(thm)],[c_987])).

cnf(c_2081,plain,
    ( ~ r1_lattice3(sK3,X0_68,X0_66)
    | ~ m1_subset_1(X0_66,u1_struct_0(sK3))
    | m1_subset_1(sK0(sK3,X0_66,X0_68),u1_struct_0(sK3))
    | k2_yellow_0(sK3,X0_68) = X0_66 ),
    inference(subtyping,[status(esa)],[c_988])).

cnf(c_2535,plain,
    ( k2_yellow_0(sK3,X0_68) = X0_66
    | r1_lattice3(sK3,X0_68,X0_66) != iProver_top
    | m1_subset_1(X0_66,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK0(sK3,X0_66,X0_68),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2081])).

cnf(c_8,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X1,sK0(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1006,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X1,sK0(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_33])).

cnf(c_1007,plain,
    ( ~ r1_lattice3(sK3,X0,X1)
    | r1_lattice3(sK3,X0,sK0(sK3,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | k2_yellow_0(sK3,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1006])).

cnf(c_1011,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r1_lattice3(sK3,X0,sK0(sK3,X1,X0))
    | ~ r1_lattice3(sK3,X0,X1)
    | k2_yellow_0(sK3,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1007,c_29,c_70])).

cnf(c_1012,plain,
    ( ~ r1_lattice3(sK3,X0,X1)
    | r1_lattice3(sK3,X0,sK0(sK3,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k2_yellow_0(sK3,X0) = X1 ),
    inference(renaming,[status(thm)],[c_1011])).

cnf(c_2080,plain,
    ( ~ r1_lattice3(sK3,X0_68,X0_66)
    | r1_lattice3(sK3,X0_68,sK0(sK3,X0_66,X0_68))
    | ~ m1_subset_1(X0_66,u1_struct_0(sK3))
    | k2_yellow_0(sK3,X0_68) = X0_66 ),
    inference(subtyping,[status(esa)],[c_1012])).

cnf(c_2536,plain,
    ( k2_yellow_0(sK3,X0_68) = X0_66
    | r1_lattice3(sK3,X0_68,X0_66) != iProver_top
    | r1_lattice3(sK3,X0_68,sK0(sK3,X0_66,X0_68)) = iProver_top
    | m1_subset_1(X0_66,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2080])).

cnf(c_21,negated_conjecture,
    ( r3_waybel_9(sK3,sK5,sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_25,negated_conjecture,
    ( v7_waybel_0(sK5) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_18,plain,
    ( ~ v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0)
    | ~ r3_waybel_9(X0,X1,X2)
    | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
    | r1_orders_2(X0,X3,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v3_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_23,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(sK3,X0),sK3,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_509,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
    | r1_orders_2(X0,X3,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(sK3))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v3_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X1)
    | k4_waybel_1(X0,sK2(X0)) != k4_waybel_1(sK3,X4)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_23])).

cnf(c_510,plain,
    ( ~ r3_waybel_9(sK3,X0,X1)
    | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
    | r1_orders_2(sK3,X2,X1)
    | ~ l1_waybel_0(X0,sK3)
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ v2_pre_topc(sK3)
    | ~ v8_pre_topc(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v1_lattice3(sK3)
    | ~ v1_compts_1(sK3)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK3)
    | ~ v7_waybel_0(X0)
    | ~ l1_waybel_9(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v2_lattice3(sK3)
    | v2_struct_0(X0)
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X3) ),
    inference(unflattening,[status(thm)],[c_509])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_36,negated_conjecture,
    ( v8_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_35,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_34,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_32,negated_conjecture,
    ( v1_lattice3(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_31,negated_conjecture,
    ( v2_lattice3(sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_30,negated_conjecture,
    ( v1_compts_1(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_514,plain,
    ( ~ v7_waybel_0(X0)
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ l1_waybel_0(X0,sK3)
    | r1_orders_2(sK3,X2,X1)
    | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
    | ~ r3_waybel_9(sK3,X0,X1)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_510,c_37,c_36,c_35,c_34,c_33,c_32,c_31,c_30,c_29])).

cnf(c_515,plain,
    ( ~ r3_waybel_9(sK3,X0,X1)
    | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
    | r1_orders_2(sK3,X2,X1)
    | ~ l1_waybel_0(X0,sK3)
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X3) ),
    inference(renaming,[status(thm)],[c_514])).

cnf(c_690,plain,
    ( ~ r3_waybel_9(sK3,X0,X1)
    | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
    | r1_orders_2(sK3,X2,X1)
    | ~ l1_waybel_0(X0,sK3)
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X3)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_515])).

cnf(c_691,plain,
    ( ~ r3_waybel_9(sK3,sK5,X0)
    | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
    | r1_orders_2(sK3,X1,X0)
    | ~ l1_waybel_0(sK5,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ v4_orders_2(sK5)
    | v2_struct_0(sK5)
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X2) ),
    inference(unflattening,[status(thm)],[c_690])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_26,negated_conjecture,
    ( v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_24,negated_conjecture,
    ( l1_waybel_0(sK5,sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_695,plain,
    ( r1_orders_2(sK3,X1,X0)
    | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
    | ~ r3_waybel_9(sK3,sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_691,c_27,c_26,c_24])).

cnf(c_696,plain,
    ( ~ r3_waybel_9(sK3,sK5,X0)
    | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
    | r1_orders_2(sK3,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X2) ),
    inference(renaming,[status(thm)],[c_695])).

cnf(c_830,plain,
    ( ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | r1_orders_2(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X2)
    | sK4 != X1
    | sK5 != sK5
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_696])).

cnf(c_831,plain,
    ( ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | r1_orders_2(sK3,X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1) ),
    inference(unflattening,[status(thm)],[c_830])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_835,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r1_orders_2(sK3,X0,sK4)
    | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_831,c_28])).

cnf(c_836,plain,
    ( ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | r1_orders_2(sK3,X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1) ),
    inference(renaming,[status(thm)],[c_835])).

cnf(c_2087,plain,
    ( ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_66)
    | r1_orders_2(sK3,X0_66,sK4)
    | ~ m1_subset_1(X1_66,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_66,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1_66) ),
    inference(subtyping,[status(esa)],[c_836])).

cnf(c_2096,plain,
    ( ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_66)
    | r1_orders_2(sK3,X0_66,sK4)
    | ~ m1_subset_1(X0_66,u1_struct_0(sK3))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_2087])).

cnf(c_2528,plain,
    ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_66) != iProver_top
    | r1_orders_2(sK3,X0_66,sK4) = iProver_top
    | m1_subset_1(X0_66,u1_struct_0(sK3)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2096])).

cnf(c_2097,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_2087])).

cnf(c_2159,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2097])).

cnf(c_2160,plain,
    ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_66) != iProver_top
    | r1_orders_2(sK3,X0_66,sK4) = iProver_top
    | m1_subset_1(X0_66,u1_struct_0(sK3)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2096])).

cnf(c_19,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
    | r1_orders_2(X0,X3,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v3_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_585,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
    | r1_orders_2(X0,X3,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | m1_subset_1(sK2(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v3_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_586,plain,
    ( ~ r3_waybel_9(sK3,X0,X1)
    | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
    | r1_orders_2(sK3,X2,X1)
    | ~ l1_waybel_0(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
    | ~ v2_pre_topc(sK3)
    | ~ v8_pre_topc(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v1_lattice3(sK3)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK3)
    | ~ v7_waybel_0(X0)
    | ~ l1_waybel_9(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v2_lattice3(sK3)
    | v2_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_585])).

cnf(c_590,plain,
    ( ~ v7_waybel_0(X0)
    | ~ r3_waybel_9(sK3,X0,X1)
    | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
    | r1_orders_2(sK3,X2,X1)
    | ~ l1_waybel_0(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_586,c_37,c_36,c_35,c_34,c_33,c_32,c_31,c_29])).

cnf(c_591,plain,
    ( ~ r3_waybel_9(sK3,X0,X1)
    | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
    | r1_orders_2(sK3,X2,X1)
    | ~ l1_waybel_0(X0,sK3)
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_590])).

cnf(c_660,plain,
    ( ~ r3_waybel_9(sK3,X0,X1)
    | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
    | r1_orders_2(sK3,X2,X1)
    | ~ l1_waybel_0(X0,sK3)
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_591])).

cnf(c_661,plain,
    ( ~ r3_waybel_9(sK3,sK5,X0)
    | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
    | r1_orders_2(sK3,X1,X0)
    | ~ l1_waybel_0(sK5,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
    | ~ v4_orders_2(sK5)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_660])).

cnf(c_665,plain,
    ( r1_orders_2(sK3,X1,X0)
    | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
    | ~ r3_waybel_9(sK3,sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_661,c_27,c_26,c_24])).

cnf(c_666,plain,
    ( ~ r3_waybel_9(sK3,sK5,X0)
    | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
    | r1_orders_2(sK3,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_665])).

cnf(c_857,plain,
    ( ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | r1_orders_2(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
    | sK4 != X1
    | sK5 != sK5
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_666])).

cnf(c_858,plain,
    ( ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | r1_orders_2(sK3,X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_857])).

cnf(c_862,plain,
    ( m1_subset_1(sK2(sK3),u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r1_orders_2(sK3,X0,sK4)
    | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_858,c_28])).

cnf(c_863,plain,
    ( ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | r1_orders_2(sK3,X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_862])).

cnf(c_2086,plain,
    ( ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_66)
    | r1_orders_2(sK3,X0_66,sK4)
    | ~ m1_subset_1(X0_66,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_863])).

cnf(c_2166,plain,
    ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_66) != iProver_top
    | r1_orders_2(sK3,X0_66,sK4) = iProver_top
    | m1_subset_1(X0_66,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2086])).

cnf(c_2095,plain,
    ( ~ m1_subset_1(X0_66,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X0_66)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_2087])).

cnf(c_2529,plain,
    ( k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X0_66)
    | m1_subset_1(X0_66,u1_struct_0(sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2095])).

cnf(c_2729,plain,
    ( m1_subset_1(sK2(sK3),u1_struct_0(sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2529])).

cnf(c_2943,plain,
    ( m1_subset_1(X0_66,u1_struct_0(sK3)) != iProver_top
    | r1_orders_2(sK3,X0_66,sK4) = iProver_top
    | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_66) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2528,c_2159,c_2160,c_2166,c_2729])).

cnf(c_2944,plain,
    ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_66) != iProver_top
    | r1_orders_2(sK3,X0_66,sK4) = iProver_top
    | m1_subset_1(X0_66,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2943])).

cnf(c_12,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_410,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_orders_2(X2)
    | X2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_2])).

cnf(c_411,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_738,plain,
    ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ l1_orders_2(X0)
    | sK5 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_411,c_24])).

cnf(c_739,plain,
    ( m1_subset_1(u1_waybel_0(sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_738])).

cnf(c_741,plain,
    ( m1_subset_1(u1_waybel_0(sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_739,c_29,c_70])).

cnf(c_2090,plain,
    ( m1_subset_1(u1_waybel_0(sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_741])).

cnf(c_2525,plain,
    ( m1_subset_1(u1_waybel_0(sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2090])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2093,plain,
    ( ~ m1_subset_1(X0_66,k1_zfmisc_1(k2_zfmisc_1(X0_69,X1_69)))
    | k2_relset_1(X0_69,X1_69,X0_66) = k2_relat_1(X0_66) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2523,plain,
    ( k2_relset_1(X0_69,X1_69,X0_66) = k2_relat_1(X0_66)
    | m1_subset_1(X0_66,k1_zfmisc_1(k2_zfmisc_1(X0_69,X1_69))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2093])).

cnf(c_2785,plain,
    ( k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)) = k2_relat_1(u1_waybel_0(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_2525,c_2523])).

cnf(c_2949,plain,
    ( r1_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_66) != iProver_top
    | r1_orders_2(sK3,X0_66,sK4) = iProver_top
    | m1_subset_1(X0_66,u1_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2944,c_2785])).

cnf(c_3059,plain,
    ( k2_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = X0_66
    | r1_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_66) != iProver_top
    | r1_orders_2(sK3,sK0(sK3,X0_66,k2_relat_1(u1_waybel_0(sK3,sK5))),sK4) = iProver_top
    | m1_subset_1(X0_66,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK0(sK3,X0_66,k2_relat_1(u1_waybel_0(sK3,sK5))),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2536,c_2949])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2094,plain,
    ( ~ m1_subset_1(X0_66,k1_zfmisc_1(k2_zfmisc_1(X0_69,X1_69)))
    | v1_relat_1(X0_66) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2522,plain,
    ( m1_subset_1(X0_66,k1_zfmisc_1(k2_zfmisc_1(X0_69,X1_69))) != iProver_top
    | v1_relat_1(X0_66) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2094])).

cnf(c_2780,plain,
    ( v1_relat_1(u1_waybel_0(sK3,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2525,c_2522])).

cnf(c_14,plain,
    ( v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_relat_1(X1)
    | k2_yellow_0(X0,k2_relat_1(X1)) = k5_yellow_2(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3,plain,
    ( ~ v2_lattice3(X0)
    | ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_647,plain,
    ( ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_31])).

cnf(c_648,plain,
    ( ~ v2_struct_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_647])).

cnf(c_106,plain,
    ( ~ v2_lattice3(sK3)
    | ~ v2_struct_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_650,plain,
    ( ~ v2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_648,c_31,c_29,c_70,c_106])).

cnf(c_775,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_relat_1(X1)
    | k2_yellow_0(X0,k2_relat_1(X1)) = k5_yellow_2(X0,X1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_650])).

cnf(c_776,plain,
    ( ~ l1_orders_2(sK3)
    | ~ v1_relat_1(X0)
    | k2_yellow_0(sK3,k2_relat_1(X0)) = k5_yellow_2(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_775])).

cnf(c_780,plain,
    ( ~ v1_relat_1(X0)
    | k2_yellow_0(sK3,k2_relat_1(X0)) = k5_yellow_2(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_776,c_29,c_70])).

cnf(c_2088,plain,
    ( ~ v1_relat_1(X0_66)
    | k2_yellow_0(sK3,k2_relat_1(X0_66)) = k5_yellow_2(sK3,X0_66) ),
    inference(subtyping,[status(esa)],[c_780])).

cnf(c_2526,plain,
    ( k2_yellow_0(sK3,k2_relat_1(X0_66)) = k5_yellow_2(sK3,X0_66)
    | v1_relat_1(X0_66) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2088])).

cnf(c_3108,plain,
    ( k2_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = k5_yellow_2(sK3,u1_waybel_0(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_2780,c_2526])).

cnf(c_13,plain,
    ( ~ l1_waybel_0(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | k5_yellow_2(X1,u1_waybel_0(X1,X0)) = k1_waybel_9(X1,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_749,plain,
    ( v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k5_yellow_2(X0,u1_waybel_0(X0,X1)) = k1_waybel_9(X0,X1)
    | sK5 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_24])).

cnf(c_750,plain,
    ( v2_struct_0(sK3)
    | ~ l1_orders_2(sK3)
    | k5_yellow_2(sK3,u1_waybel_0(sK3,sK5)) = k1_waybel_9(sK3,sK5) ),
    inference(unflattening,[status(thm)],[c_749])).

cnf(c_752,plain,
    ( k5_yellow_2(sK3,u1_waybel_0(sK3,sK5)) = k1_waybel_9(sK3,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_750,c_31,c_29,c_70,c_106])).

cnf(c_2089,plain,
    ( k5_yellow_2(sK3,u1_waybel_0(sK3,sK5)) = k1_waybel_9(sK3,sK5) ),
    inference(subtyping,[status(esa)],[c_752])).

cnf(c_3109,plain,
    ( k2_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = k1_waybel_9(sK3,sK5) ),
    inference(light_normalisation,[status(thm)],[c_3108,c_2089])).

cnf(c_3252,plain,
    ( k1_waybel_9(sK3,sK5) = X0_66
    | r1_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_66) != iProver_top
    | r1_orders_2(sK3,sK0(sK3,X0_66,k2_relat_1(u1_waybel_0(sK3,sK5))),sK4) = iProver_top
    | m1_subset_1(X0_66,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK0(sK3,X0_66,k2_relat_1(u1_waybel_0(sK3,sK5))),u1_struct_0(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3059,c_3109])).

cnf(c_3262,plain,
    ( k1_waybel_9(sK3,sK5) = X0_66
    | k2_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = X0_66
    | r1_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_66) != iProver_top
    | r1_orders_2(sK3,sK0(sK3,X0_66,k2_relat_1(u1_waybel_0(sK3,sK5))),sK4) = iProver_top
    | m1_subset_1(X0_66,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2535,c_3252])).

cnf(c_3268,plain,
    ( k1_waybel_9(sK3,sK5) = X0_66
    | r1_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_66) != iProver_top
    | r1_orders_2(sK3,sK0(sK3,X0_66,k2_relat_1(u1_waybel_0(sK3,sK5))),sK4) = iProver_top
    | m1_subset_1(X0_66,u1_struct_0(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3262,c_3109])).

cnf(c_7,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK0(X0,X2,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1030,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK0(X0,X2,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_33])).

cnf(c_1031,plain,
    ( ~ r1_lattice3(sK3,X0,X1)
    | ~ r1_orders_2(sK3,sK0(sK3,X1,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | k2_yellow_0(sK3,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1030])).

cnf(c_1035,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r1_orders_2(sK3,sK0(sK3,X1,X0),X1)
    | ~ r1_lattice3(sK3,X0,X1)
    | k2_yellow_0(sK3,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1031,c_29,c_70])).

cnf(c_1036,plain,
    ( ~ r1_lattice3(sK3,X0,X1)
    | ~ r1_orders_2(sK3,sK0(sK3,X1,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k2_yellow_0(sK3,X0) = X1 ),
    inference(renaming,[status(thm)],[c_1035])).

cnf(c_2079,plain,
    ( ~ r1_lattice3(sK3,X0_68,X0_66)
    | ~ r1_orders_2(sK3,sK0(sK3,X0_66,X0_68),X0_66)
    | ~ m1_subset_1(X0_66,u1_struct_0(sK3))
    | k2_yellow_0(sK3,X0_68) = X0_66 ),
    inference(subtyping,[status(esa)],[c_1036])).

cnf(c_2537,plain,
    ( k2_yellow_0(sK3,X0_68) = X0_66
    | r1_lattice3(sK3,X0_68,X0_66) != iProver_top
    | r1_orders_2(sK3,sK0(sK3,X0_66,X0_68),X0_66) != iProver_top
    | m1_subset_1(X0_66,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2079])).

cnf(c_3470,plain,
    ( k1_waybel_9(sK3,sK5) = sK4
    | k2_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = sK4
    | r1_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),sK4) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3268,c_2537])).

cnf(c_3475,plain,
    ( k1_waybel_9(sK3,sK5) = sK4
    | r1_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),sK4) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3470,c_3109])).

cnf(c_16,plain,
    ( ~ v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0)
    | ~ r3_waybel_9(X0,X1,X2)
    | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
    | ~ v11_waybel_0(X1,X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v3_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_22,negated_conjecture,
    ( v11_waybel_0(sK5,sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_475,plain,
    ( ~ v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0)
    | ~ r3_waybel_9(X0,X1,X2)
    | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v3_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X1)
    | sK5 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_476,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK3,sK1(sK3)),sK3,sK3)
    | ~ r3_waybel_9(sK3,sK5,X0)
    | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | ~ l1_waybel_0(sK5,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ v2_pre_topc(sK3)
    | ~ v8_pre_topc(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v1_lattice3(sK3)
    | ~ v1_compts_1(sK3)
    | ~ v4_orders_2(sK5)
    | ~ v4_orders_2(sK3)
    | ~ v7_waybel_0(sK5)
    | ~ l1_waybel_9(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v2_lattice3(sK3)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_475])).

cnf(c_480,plain,
    ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | ~ r3_waybel_9(sK3,sK5,X0)
    | ~ v5_pre_topc(k4_waybel_1(sK3,sK1(sK3)),sK3,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_476,c_37,c_36,c_35,c_34,c_33,c_32,c_31,c_30,c_29,c_27,c_26,c_25,c_24])).

cnf(c_481,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK3,sK1(sK3)),sK3,sK3)
    | ~ r3_waybel_9(sK3,sK5,X0)
    | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_480])).

cnf(c_554,plain,
    ( ~ r3_waybel_9(sK3,sK5,X0)
    | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X1)
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_481])).

cnf(c_881,plain,
    ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X1)
    | sK4 != X0
    | sK5 != sK5
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_554])).

cnf(c_882,plain,
    ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_881])).

cnf(c_886,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
    | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_882,c_28])).

cnf(c_887,plain,
    ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0) ),
    inference(renaming,[status(thm)],[c_886])).

cnf(c_2085,plain,
    ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
    | ~ m1_subset_1(X0_66,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0_66) ),
    inference(subtyping,[status(esa)],[c_887])).

cnf(c_2531,plain,
    ( k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0_66)
    | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) = iProver_top
    | m1_subset_1(X0_66,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2085])).

cnf(c_17,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
    | ~ v11_waybel_0(X1,X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v3_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_451,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v3_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X1)
    | sK5 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_22])).

cnf(c_452,plain,
    ( ~ r3_waybel_9(sK3,sK5,X0)
    | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | ~ l1_waybel_0(sK5,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3),u1_struct_0(sK3))
    | ~ v2_pre_topc(sK3)
    | ~ v8_pre_topc(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v1_lattice3(sK3)
    | ~ v1_compts_1(sK3)
    | ~ v4_orders_2(sK5)
    | ~ v4_orders_2(sK3)
    | ~ v7_waybel_0(sK5)
    | ~ l1_waybel_9(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v2_lattice3(sK3)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_451])).

cnf(c_456,plain,
    ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | ~ r3_waybel_9(sK3,sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_452,c_37,c_36,c_35,c_34,c_33,c_32,c_31,c_30,c_29,c_27,c_26,c_25,c_24])).

cnf(c_457,plain,
    ( ~ r3_waybel_9(sK3,sK5,X0)
    | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_456])).

cnf(c_902,plain,
    ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3),u1_struct_0(sK3))
    | sK4 != X0
    | sK5 != sK5
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_457])).

cnf(c_903,plain,
    ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
    | m1_subset_1(sK1(sK3),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_902])).

cnf(c_905,plain,
    ( m1_subset_1(sK1(sK3),u1_struct_0(sK3))
    | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_903,c_28])).

cnf(c_906,plain,
    ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
    | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_905])).

cnf(c_907,plain,
    ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) = iProver_top
    | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_906])).

cnf(c_2103,plain,
    ( X0_70 = X0_70 ),
    theory(equality)).

cnf(c_2718,plain,
    ( k4_waybel_1(sK3,sK1(sK3)) = k4_waybel_1(sK3,sK1(sK3)) ),
    inference(instantiation,[status(thm)],[c_2103])).

cnf(c_2719,plain,
    ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
    | ~ m1_subset_1(sK1(sK3),u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,sK1(sK3)) ),
    inference(instantiation,[status(thm)],[c_2085])).

cnf(c_2720,plain,
    ( k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,sK1(sK3))
    | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) = iProver_top
    | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2719])).

cnf(c_2758,plain,
    ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2531,c_907,c_2718,c_2720])).

cnf(c_2837,plain,
    ( r1_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2785,c_2758])).

cnf(c_20,negated_conjecture,
    ( k1_waybel_9(sK3,sK5) != sK4 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2092,negated_conjecture,
    ( k1_waybel_9(sK3,sK5) != sK4 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_47,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3475,c_2837,c_2092,c_47])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:55:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.95/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/0.98  
% 1.95/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.95/0.98  
% 1.95/0.98  ------  iProver source info
% 1.95/0.98  
% 1.95/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.95/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.95/0.98  git: non_committed_changes: false
% 1.95/0.98  git: last_make_outside_of_git: false
% 1.95/0.98  
% 1.95/0.98  ------ 
% 1.95/0.98  
% 1.95/0.98  ------ Input Options
% 1.95/0.98  
% 1.95/0.98  --out_options                           all
% 1.95/0.98  --tptp_safe_out                         true
% 1.95/0.98  --problem_path                          ""
% 1.95/0.98  --include_path                          ""
% 1.95/0.98  --clausifier                            res/vclausify_rel
% 1.95/0.98  --clausifier_options                    --mode clausify
% 1.95/0.98  --stdin                                 false
% 1.95/0.98  --stats_out                             all
% 1.95/0.98  
% 1.95/0.98  ------ General Options
% 1.95/0.98  
% 1.95/0.98  --fof                                   false
% 1.95/0.98  --time_out_real                         305.
% 1.95/0.98  --time_out_virtual                      -1.
% 1.95/0.98  --symbol_type_check                     false
% 1.95/0.98  --clausify_out                          false
% 1.95/0.98  --sig_cnt_out                           false
% 1.95/0.98  --trig_cnt_out                          false
% 1.95/0.98  --trig_cnt_out_tolerance                1.
% 1.95/0.98  --trig_cnt_out_sk_spl                   false
% 1.95/0.98  --abstr_cl_out                          false
% 1.95/0.98  
% 1.95/0.98  ------ Global Options
% 1.95/0.98  
% 1.95/0.98  --schedule                              default
% 1.95/0.98  --add_important_lit                     false
% 1.95/0.98  --prop_solver_per_cl                    1000
% 1.95/0.98  --min_unsat_core                        false
% 1.95/0.98  --soft_assumptions                      false
% 1.95/0.98  --soft_lemma_size                       3
% 1.95/0.98  --prop_impl_unit_size                   0
% 1.95/0.98  --prop_impl_unit                        []
% 1.95/0.98  --share_sel_clauses                     true
% 1.95/0.98  --reset_solvers                         false
% 1.95/0.98  --bc_imp_inh                            [conj_cone]
% 1.95/0.98  --conj_cone_tolerance                   3.
% 1.95/0.98  --extra_neg_conj                        none
% 1.95/0.98  --large_theory_mode                     true
% 1.95/0.98  --prolific_symb_bound                   200
% 1.95/0.98  --lt_threshold                          2000
% 1.95/0.98  --clause_weak_htbl                      true
% 1.95/0.98  --gc_record_bc_elim                     false
% 1.95/0.98  
% 1.95/0.98  ------ Preprocessing Options
% 1.95/0.98  
% 1.95/0.98  --preprocessing_flag                    true
% 1.95/0.98  --time_out_prep_mult                    0.1
% 1.95/0.98  --splitting_mode                        input
% 1.95/0.98  --splitting_grd                         true
% 1.95/0.98  --splitting_cvd                         false
% 1.95/0.98  --splitting_cvd_svl                     false
% 1.95/0.98  --splitting_nvd                         32
% 1.95/0.98  --sub_typing                            true
% 1.95/0.98  --prep_gs_sim                           true
% 1.95/0.98  --prep_unflatten                        true
% 1.95/0.98  --prep_res_sim                          true
% 1.95/0.98  --prep_upred                            true
% 1.95/0.98  --prep_sem_filter                       exhaustive
% 1.95/0.98  --prep_sem_filter_out                   false
% 1.95/0.98  --pred_elim                             true
% 1.95/0.98  --res_sim_input                         true
% 1.95/0.98  --eq_ax_congr_red                       true
% 1.95/0.98  --pure_diseq_elim                       true
% 1.95/0.98  --brand_transform                       false
% 1.95/0.98  --non_eq_to_eq                          false
% 1.95/0.98  --prep_def_merge                        true
% 1.95/0.98  --prep_def_merge_prop_impl              false
% 1.95/0.98  --prep_def_merge_mbd                    true
% 1.95/0.98  --prep_def_merge_tr_red                 false
% 1.95/0.98  --prep_def_merge_tr_cl                  false
% 1.95/0.98  --smt_preprocessing                     true
% 1.95/0.98  --smt_ac_axioms                         fast
% 1.95/0.98  --preprocessed_out                      false
% 1.95/0.98  --preprocessed_stats                    false
% 1.95/0.98  
% 1.95/0.98  ------ Abstraction refinement Options
% 1.95/0.98  
% 1.95/0.98  --abstr_ref                             []
% 1.95/0.98  --abstr_ref_prep                        false
% 1.95/0.98  --abstr_ref_until_sat                   false
% 1.95/0.98  --abstr_ref_sig_restrict                funpre
% 1.95/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.95/0.98  --abstr_ref_under                       []
% 1.95/0.98  
% 1.95/0.98  ------ SAT Options
% 1.95/0.98  
% 1.95/0.98  --sat_mode                              false
% 1.95/0.98  --sat_fm_restart_options                ""
% 1.95/0.98  --sat_gr_def                            false
% 1.95/0.98  --sat_epr_types                         true
% 1.95/0.98  --sat_non_cyclic_types                  false
% 1.95/0.98  --sat_finite_models                     false
% 1.95/0.98  --sat_fm_lemmas                         false
% 1.95/0.98  --sat_fm_prep                           false
% 1.95/0.98  --sat_fm_uc_incr                        true
% 1.95/0.98  --sat_out_model                         small
% 1.95/0.98  --sat_out_clauses                       false
% 1.95/0.98  
% 1.95/0.98  ------ QBF Options
% 1.95/0.98  
% 1.95/0.98  --qbf_mode                              false
% 1.95/0.98  --qbf_elim_univ                         false
% 1.95/0.98  --qbf_dom_inst                          none
% 1.95/0.98  --qbf_dom_pre_inst                      false
% 1.95/0.98  --qbf_sk_in                             false
% 1.95/0.98  --qbf_pred_elim                         true
% 1.95/0.98  --qbf_split                             512
% 1.95/0.98  
% 1.95/0.98  ------ BMC1 Options
% 1.95/0.98  
% 1.95/0.98  --bmc1_incremental                      false
% 1.95/0.98  --bmc1_axioms                           reachable_all
% 1.95/0.98  --bmc1_min_bound                        0
% 1.95/0.98  --bmc1_max_bound                        -1
% 1.95/0.98  --bmc1_max_bound_default                -1
% 1.95/0.98  --bmc1_symbol_reachability              true
% 1.95/0.98  --bmc1_property_lemmas                  false
% 1.95/0.98  --bmc1_k_induction                      false
% 1.95/0.98  --bmc1_non_equiv_states                 false
% 1.95/0.98  --bmc1_deadlock                         false
% 1.95/0.98  --bmc1_ucm                              false
% 1.95/0.98  --bmc1_add_unsat_core                   none
% 1.95/0.98  --bmc1_unsat_core_children              false
% 1.95/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.95/0.98  --bmc1_out_stat                         full
% 1.95/0.98  --bmc1_ground_init                      false
% 1.95/0.98  --bmc1_pre_inst_next_state              false
% 1.95/0.98  --bmc1_pre_inst_state                   false
% 1.95/0.98  --bmc1_pre_inst_reach_state             false
% 1.95/0.98  --bmc1_out_unsat_core                   false
% 1.95/0.98  --bmc1_aig_witness_out                  false
% 1.95/0.98  --bmc1_verbose                          false
% 1.95/0.98  --bmc1_dump_clauses_tptp                false
% 1.95/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.95/0.98  --bmc1_dump_file                        -
% 1.95/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.95/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.95/0.98  --bmc1_ucm_extend_mode                  1
% 1.95/0.98  --bmc1_ucm_init_mode                    2
% 1.95/0.98  --bmc1_ucm_cone_mode                    none
% 1.95/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.95/0.98  --bmc1_ucm_relax_model                  4
% 1.95/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.95/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.95/0.98  --bmc1_ucm_layered_model                none
% 1.95/0.98  --bmc1_ucm_max_lemma_size               10
% 1.95/0.98  
% 1.95/0.98  ------ AIG Options
% 1.95/0.98  
% 1.95/0.98  --aig_mode                              false
% 1.95/0.98  
% 1.95/0.98  ------ Instantiation Options
% 1.95/0.98  
% 1.95/0.98  --instantiation_flag                    true
% 1.95/0.98  --inst_sos_flag                         false
% 1.95/0.98  --inst_sos_phase                        true
% 1.95/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.95/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.95/0.98  --inst_lit_sel_side                     num_symb
% 1.95/0.98  --inst_solver_per_active                1400
% 1.95/0.98  --inst_solver_calls_frac                1.
% 1.95/0.98  --inst_passive_queue_type               priority_queues
% 1.95/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.95/0.98  --inst_passive_queues_freq              [25;2]
% 1.95/0.98  --inst_dismatching                      true
% 1.95/0.98  --inst_eager_unprocessed_to_passive     true
% 1.95/0.98  --inst_prop_sim_given                   true
% 1.95/0.98  --inst_prop_sim_new                     false
% 1.95/0.98  --inst_subs_new                         false
% 1.95/0.98  --inst_eq_res_simp                      false
% 1.95/0.98  --inst_subs_given                       false
% 1.95/0.98  --inst_orphan_elimination               true
% 1.95/0.98  --inst_learning_loop_flag               true
% 1.95/0.98  --inst_learning_start                   3000
% 1.95/0.98  --inst_learning_factor                  2
% 1.95/0.98  --inst_start_prop_sim_after_learn       3
% 1.95/0.98  --inst_sel_renew                        solver
% 1.95/0.98  --inst_lit_activity_flag                true
% 1.95/0.98  --inst_restr_to_given                   false
% 1.95/0.98  --inst_activity_threshold               500
% 1.95/0.98  --inst_out_proof                        true
% 1.95/0.98  
% 1.95/0.98  ------ Resolution Options
% 1.95/0.98  
% 1.95/0.98  --resolution_flag                       true
% 1.95/0.98  --res_lit_sel                           adaptive
% 1.95/0.98  --res_lit_sel_side                      none
% 1.95/0.98  --res_ordering                          kbo
% 1.95/0.98  --res_to_prop_solver                    active
% 1.95/0.98  --res_prop_simpl_new                    false
% 1.95/0.98  --res_prop_simpl_given                  true
% 1.95/0.98  --res_passive_queue_type                priority_queues
% 1.95/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.95/0.98  --res_passive_queues_freq               [15;5]
% 1.95/0.98  --res_forward_subs                      full
% 1.95/0.98  --res_backward_subs                     full
% 1.95/0.98  --res_forward_subs_resolution           true
% 1.95/0.98  --res_backward_subs_resolution          true
% 1.95/0.98  --res_orphan_elimination                true
% 1.95/0.98  --res_time_limit                        2.
% 1.95/0.98  --res_out_proof                         true
% 1.95/0.98  
% 1.95/0.98  ------ Superposition Options
% 1.95/0.98  
% 1.95/0.98  --superposition_flag                    true
% 1.95/0.98  --sup_passive_queue_type                priority_queues
% 1.95/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.95/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.95/0.98  --demod_completeness_check              fast
% 1.95/0.98  --demod_use_ground                      true
% 1.95/0.98  --sup_to_prop_solver                    passive
% 1.95/0.98  --sup_prop_simpl_new                    true
% 1.95/0.98  --sup_prop_simpl_given                  true
% 1.95/0.98  --sup_fun_splitting                     false
% 1.95/0.98  --sup_smt_interval                      50000
% 1.95/0.98  
% 1.95/0.98  ------ Superposition Simplification Setup
% 1.95/0.98  
% 1.95/0.98  --sup_indices_passive                   []
% 1.95/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.95/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.95/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.95/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.95/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.95/0.98  --sup_full_bw                           [BwDemod]
% 1.95/0.98  --sup_immed_triv                        [TrivRules]
% 1.95/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.95/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.95/0.98  --sup_immed_bw_main                     []
% 1.95/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.95/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.95/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.95/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.95/0.98  
% 1.95/0.98  ------ Combination Options
% 1.95/0.98  
% 1.95/0.98  --comb_res_mult                         3
% 1.95/0.98  --comb_sup_mult                         2
% 1.95/0.98  --comb_inst_mult                        10
% 1.95/0.98  
% 1.95/0.98  ------ Debug Options
% 1.95/0.98  
% 1.95/0.98  --dbg_backtrace                         false
% 1.95/0.98  --dbg_dump_prop_clauses                 false
% 1.95/0.98  --dbg_dump_prop_clauses_file            -
% 1.95/0.98  --dbg_out_stat                          false
% 1.95/0.98  ------ Parsing...
% 1.95/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.95/0.98  
% 1.95/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe:16:0s pe_e  sf_s  rm: 16 0s  sf_e  pe_s  pe_e 
% 1.95/0.98  
% 1.95/0.98  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.95/0.98  
% 1.95/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.95/0.98  ------ Proving...
% 1.95/0.98  ------ Problem Properties 
% 1.95/0.98  
% 1.95/0.98  
% 1.95/0.98  clauses                                 22
% 1.95/0.98  conjectures                             2
% 1.95/0.98  EPR                                     1
% 1.95/0.98  Horn                                    15
% 1.95/0.98  unary                                   4
% 1.95/0.98  binary                                  5
% 1.95/0.98  lits                                    63
% 1.95/0.98  lits eq                                 11
% 1.95/0.98  fd_pure                                 0
% 1.95/0.98  fd_pseudo                               0
% 1.95/0.98  fd_cond                                 0
% 1.95/0.98  fd_pseudo_cond                          3
% 1.95/0.98  AC symbols                              0
% 1.95/0.98  
% 1.95/0.98  ------ Schedule dynamic 5 is on 
% 1.95/0.98  
% 1.95/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.95/0.98  
% 1.95/0.98  
% 1.95/0.98  ------ 
% 1.95/0.98  Current options:
% 1.95/0.98  ------ 
% 1.95/0.98  
% 1.95/0.98  ------ Input Options
% 1.95/0.98  
% 1.95/0.98  --out_options                           all
% 1.95/0.98  --tptp_safe_out                         true
% 1.95/0.98  --problem_path                          ""
% 1.95/0.98  --include_path                          ""
% 1.95/0.98  --clausifier                            res/vclausify_rel
% 1.95/0.98  --clausifier_options                    --mode clausify
% 1.95/0.98  --stdin                                 false
% 1.95/0.98  --stats_out                             all
% 1.95/0.98  
% 1.95/0.98  ------ General Options
% 1.95/0.98  
% 1.95/0.98  --fof                                   false
% 1.95/0.98  --time_out_real                         305.
% 1.95/0.98  --time_out_virtual                      -1.
% 1.95/0.98  --symbol_type_check                     false
% 1.95/0.98  --clausify_out                          false
% 1.95/0.98  --sig_cnt_out                           false
% 1.95/0.98  --trig_cnt_out                          false
% 1.95/0.98  --trig_cnt_out_tolerance                1.
% 1.95/0.98  --trig_cnt_out_sk_spl                   false
% 1.95/0.98  --abstr_cl_out                          false
% 1.95/0.98  
% 1.95/0.98  ------ Global Options
% 1.95/0.98  
% 1.95/0.98  --schedule                              default
% 1.95/0.98  --add_important_lit                     false
% 1.95/0.98  --prop_solver_per_cl                    1000
% 1.95/0.98  --min_unsat_core                        false
% 1.95/0.98  --soft_assumptions                      false
% 1.95/0.98  --soft_lemma_size                       3
% 1.95/0.98  --prop_impl_unit_size                   0
% 1.95/0.98  --prop_impl_unit                        []
% 1.95/0.98  --share_sel_clauses                     true
% 1.95/0.98  --reset_solvers                         false
% 1.95/0.98  --bc_imp_inh                            [conj_cone]
% 1.95/0.98  --conj_cone_tolerance                   3.
% 1.95/0.98  --extra_neg_conj                        none
% 1.95/0.98  --large_theory_mode                     true
% 1.95/0.98  --prolific_symb_bound                   200
% 1.95/0.98  --lt_threshold                          2000
% 1.95/0.98  --clause_weak_htbl                      true
% 1.95/0.98  --gc_record_bc_elim                     false
% 1.95/0.98  
% 1.95/0.98  ------ Preprocessing Options
% 1.95/0.98  
% 1.95/0.98  --preprocessing_flag                    true
% 1.95/0.98  --time_out_prep_mult                    0.1
% 1.95/0.98  --splitting_mode                        input
% 1.95/0.98  --splitting_grd                         true
% 1.95/0.98  --splitting_cvd                         false
% 1.95/0.98  --splitting_cvd_svl                     false
% 1.95/0.98  --splitting_nvd                         32
% 1.95/0.98  --sub_typing                            true
% 1.95/0.98  --prep_gs_sim                           true
% 1.95/0.98  --prep_unflatten                        true
% 1.95/0.98  --prep_res_sim                          true
% 1.95/0.98  --prep_upred                            true
% 1.95/0.98  --prep_sem_filter                       exhaustive
% 1.95/0.98  --prep_sem_filter_out                   false
% 1.95/0.98  --pred_elim                             true
% 1.95/0.98  --res_sim_input                         true
% 1.95/0.98  --eq_ax_congr_red                       true
% 1.95/0.98  --pure_diseq_elim                       true
% 1.95/0.98  --brand_transform                       false
% 1.95/0.98  --non_eq_to_eq                          false
% 1.95/0.98  --prep_def_merge                        true
% 1.95/0.98  --prep_def_merge_prop_impl              false
% 1.95/0.98  --prep_def_merge_mbd                    true
% 1.95/0.98  --prep_def_merge_tr_red                 false
% 1.95/0.98  --prep_def_merge_tr_cl                  false
% 1.95/0.98  --smt_preprocessing                     true
% 1.95/0.98  --smt_ac_axioms                         fast
% 1.95/0.98  --preprocessed_out                      false
% 1.95/0.98  --preprocessed_stats                    false
% 1.95/0.98  
% 1.95/0.98  ------ Abstraction refinement Options
% 1.95/0.98  
% 1.95/0.98  --abstr_ref                             []
% 1.95/0.98  --abstr_ref_prep                        false
% 1.95/0.98  --abstr_ref_until_sat                   false
% 1.95/0.98  --abstr_ref_sig_restrict                funpre
% 1.95/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.95/0.98  --abstr_ref_under                       []
% 1.95/0.98  
% 1.95/0.98  ------ SAT Options
% 1.95/0.98  
% 1.95/0.98  --sat_mode                              false
% 1.95/0.98  --sat_fm_restart_options                ""
% 1.95/0.98  --sat_gr_def                            false
% 1.95/0.98  --sat_epr_types                         true
% 1.95/0.98  --sat_non_cyclic_types                  false
% 1.95/0.98  --sat_finite_models                     false
% 1.95/0.98  --sat_fm_lemmas                         false
% 1.95/0.98  --sat_fm_prep                           false
% 1.95/0.98  --sat_fm_uc_incr                        true
% 1.95/0.98  --sat_out_model                         small
% 1.95/0.98  --sat_out_clauses                       false
% 1.95/0.98  
% 1.95/0.98  ------ QBF Options
% 1.95/0.98  
% 1.95/0.98  --qbf_mode                              false
% 1.95/0.98  --qbf_elim_univ                         false
% 1.95/0.98  --qbf_dom_inst                          none
% 1.95/0.98  --qbf_dom_pre_inst                      false
% 1.95/0.98  --qbf_sk_in                             false
% 1.95/0.98  --qbf_pred_elim                         true
% 1.95/0.98  --qbf_split                             512
% 1.95/0.98  
% 1.95/0.98  ------ BMC1 Options
% 1.95/0.98  
% 1.95/0.98  --bmc1_incremental                      false
% 1.95/0.98  --bmc1_axioms                           reachable_all
% 1.95/0.98  --bmc1_min_bound                        0
% 1.95/0.98  --bmc1_max_bound                        -1
% 1.95/0.98  --bmc1_max_bound_default                -1
% 1.95/0.98  --bmc1_symbol_reachability              true
% 1.95/0.98  --bmc1_property_lemmas                  false
% 1.95/0.98  --bmc1_k_induction                      false
% 1.95/0.98  --bmc1_non_equiv_states                 false
% 1.95/0.98  --bmc1_deadlock                         false
% 1.95/0.98  --bmc1_ucm                              false
% 1.95/0.98  --bmc1_add_unsat_core                   none
% 1.95/0.98  --bmc1_unsat_core_children              false
% 1.95/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.95/0.98  --bmc1_out_stat                         full
% 1.95/0.98  --bmc1_ground_init                      false
% 1.95/0.98  --bmc1_pre_inst_next_state              false
% 1.95/0.98  --bmc1_pre_inst_state                   false
% 1.95/0.98  --bmc1_pre_inst_reach_state             false
% 1.95/0.98  --bmc1_out_unsat_core                   false
% 1.95/0.98  --bmc1_aig_witness_out                  false
% 1.95/0.98  --bmc1_verbose                          false
% 1.95/0.98  --bmc1_dump_clauses_tptp                false
% 1.95/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.95/0.98  --bmc1_dump_file                        -
% 1.95/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.95/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.95/0.98  --bmc1_ucm_extend_mode                  1
% 1.95/0.98  --bmc1_ucm_init_mode                    2
% 1.95/0.98  --bmc1_ucm_cone_mode                    none
% 1.95/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.95/0.98  --bmc1_ucm_relax_model                  4
% 1.95/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.95/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.95/0.98  --bmc1_ucm_layered_model                none
% 1.95/0.98  --bmc1_ucm_max_lemma_size               10
% 1.95/0.98  
% 1.95/0.98  ------ AIG Options
% 1.95/0.98  
% 1.95/0.98  --aig_mode                              false
% 1.95/0.98  
% 1.95/0.98  ------ Instantiation Options
% 1.95/0.98  
% 1.95/0.98  --instantiation_flag                    true
% 1.95/0.98  --inst_sos_flag                         false
% 1.95/0.98  --inst_sos_phase                        true
% 1.95/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.95/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.95/0.98  --inst_lit_sel_side                     none
% 1.95/0.98  --inst_solver_per_active                1400
% 1.95/0.98  --inst_solver_calls_frac                1.
% 1.95/0.98  --inst_passive_queue_type               priority_queues
% 1.95/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.95/0.98  --inst_passive_queues_freq              [25;2]
% 1.95/0.98  --inst_dismatching                      true
% 1.95/0.98  --inst_eager_unprocessed_to_passive     true
% 1.95/0.98  --inst_prop_sim_given                   true
% 1.95/0.98  --inst_prop_sim_new                     false
% 1.95/0.98  --inst_subs_new                         false
% 1.95/0.98  --inst_eq_res_simp                      false
% 1.95/0.98  --inst_subs_given                       false
% 1.95/0.98  --inst_orphan_elimination               true
% 1.95/0.98  --inst_learning_loop_flag               true
% 1.95/0.98  --inst_learning_start                   3000
% 1.95/0.98  --inst_learning_factor                  2
% 1.95/0.98  --inst_start_prop_sim_after_learn       3
% 1.95/0.98  --inst_sel_renew                        solver
% 1.95/0.98  --inst_lit_activity_flag                true
% 1.95/0.98  --inst_restr_to_given                   false
% 1.95/0.98  --inst_activity_threshold               500
% 1.95/0.98  --inst_out_proof                        true
% 1.95/0.98  
% 1.95/0.98  ------ Resolution Options
% 1.95/0.98  
% 1.95/0.98  --resolution_flag                       false
% 1.95/0.98  --res_lit_sel                           adaptive
% 1.95/0.98  --res_lit_sel_side                      none
% 1.95/0.98  --res_ordering                          kbo
% 1.95/0.98  --res_to_prop_solver                    active
% 1.95/0.98  --res_prop_simpl_new                    false
% 1.95/0.98  --res_prop_simpl_given                  true
% 1.95/0.98  --res_passive_queue_type                priority_queues
% 1.95/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.95/0.98  --res_passive_queues_freq               [15;5]
% 1.95/0.98  --res_forward_subs                      full
% 1.95/0.98  --res_backward_subs                     full
% 1.95/0.98  --res_forward_subs_resolution           true
% 1.95/0.98  --res_backward_subs_resolution          true
% 1.95/0.98  --res_orphan_elimination                true
% 1.95/0.98  --res_time_limit                        2.
% 1.95/0.98  --res_out_proof                         true
% 1.95/0.98  
% 1.95/0.98  ------ Superposition Options
% 1.95/0.98  
% 1.95/0.98  --superposition_flag                    true
% 1.95/0.98  --sup_passive_queue_type                priority_queues
% 1.95/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.95/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.95/0.98  --demod_completeness_check              fast
% 1.95/0.98  --demod_use_ground                      true
% 1.95/0.98  --sup_to_prop_solver                    passive
% 1.95/0.98  --sup_prop_simpl_new                    true
% 1.95/0.98  --sup_prop_simpl_given                  true
% 1.95/0.98  --sup_fun_splitting                     false
% 1.95/0.98  --sup_smt_interval                      50000
% 1.95/0.98  
% 1.95/0.98  ------ Superposition Simplification Setup
% 1.95/0.98  
% 1.95/0.98  --sup_indices_passive                   []
% 1.95/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.95/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.95/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.95/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.95/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.95/0.98  --sup_full_bw                           [BwDemod]
% 1.95/0.98  --sup_immed_triv                        [TrivRules]
% 1.95/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.95/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.95/0.98  --sup_immed_bw_main                     []
% 1.95/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.95/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.95/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.95/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.95/0.98  
% 1.95/0.98  ------ Combination Options
% 1.95/0.98  
% 1.95/0.98  --comb_res_mult                         3
% 1.95/0.98  --comb_sup_mult                         2
% 1.95/0.98  --comb_inst_mult                        10
% 1.95/0.98  
% 1.95/0.98  ------ Debug Options
% 1.95/0.98  
% 1.95/0.98  --dbg_backtrace                         false
% 1.95/0.98  --dbg_dump_prop_clauses                 false
% 1.95/0.98  --dbg_dump_prop_clauses_file            -
% 1.95/0.98  --dbg_out_stat                          false
% 1.95/0.98  
% 1.95/0.98  
% 1.95/0.98  
% 1.95/0.98  
% 1.95/0.98  ------ Proving...
% 1.95/0.98  
% 1.95/0.98  
% 1.95/0.98  % SZS status Theorem for theBenchmark.p
% 1.95/0.98  
% 1.95/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.95/0.98  
% 1.95/0.98  fof(f5,axiom,(
% 1.95/0.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1)) => (r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1)) & ((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1))))))),
% 1.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.95/0.98  
% 1.95/0.98  fof(f14,plain,(
% 1.95/0.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1)) => (r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1)) & ((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X4) => r1_orders_2(X0,X4,X1))) & r1_lattice3(X0,X2,X1))))))),
% 1.95/0.98    inference(rectify,[],[f5])).
% 1.95/0.98  
% 1.95/0.98  fof(f24,plain,(
% 1.95/0.98    ! [X0] : (! [X1] : (! [X2] : (((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | (~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 1.95/0.98    inference(ennf_transformation,[],[f14])).
% 1.95/0.98  
% 1.95/0.98  fof(f25,plain,(
% 1.95/0.98    ! [X0] : (! [X1] : (! [X2] : (((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | ~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 1.95/0.98    inference(flattening,[],[f24])).
% 1.95/0.98  
% 1.95/0.98  fof(f39,plain,(
% 1.95/0.98    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK0(X0,X1,X2),X1) & r1_lattice3(X0,X2,sK0(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 1.95/0.98    introduced(choice_axiom,[])).
% 1.95/0.98  
% 1.95/0.98  fof(f40,plain,(
% 1.95/0.98    ! [X0] : (! [X1] : (! [X2] : (((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) | (~r1_orders_2(X0,sK0(X0,X1,X2),X1) & r1_lattice3(X0,X2,sK0(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | ~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 1.95/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f39])).
% 1.95/0.98  
% 1.95/0.98  fof(f56,plain,(
% 1.95/0.98    ( ! [X2,X0,X1] : (k2_yellow_0(X0,X2) = X1 | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 1.95/0.98    inference(cnf_transformation,[],[f40])).
% 1.95/0.98  
% 1.95/0.98  fof(f12,conjecture,(
% 1.95/0.98    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => ((r3_waybel_9(X0,X2,X1) & v11_waybel_0(X2,X0) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0))) => k1_waybel_9(X0,X2) = X1))))),
% 1.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.95/0.98  
% 1.95/0.98  fof(f13,negated_conjecture,(
% 1.95/0.98    ~! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => ((r3_waybel_9(X0,X2,X1) & v11_waybel_0(X2,X0) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0))) => k1_waybel_9(X0,X2) = X1))))),
% 1.95/0.98    inference(negated_conjecture,[],[f12])).
% 1.95/0.98  
% 1.95/0.98  fof(f37,plain,(
% 1.95/0.98    ? [X0] : (? [X1] : (? [X2] : ((k1_waybel_9(X0,X2) != X1 & (r3_waybel_9(X0,X2,X1) & v11_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))))) & (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.95/0.98    inference(ennf_transformation,[],[f13])).
% 1.95/0.98  
% 1.95/0.98  fof(f38,plain,(
% 1.95/0.98    ? [X0] : (? [X1] : (? [X2] : (k1_waybel_9(X0,X2) != X1 & r3_waybel_9(X0,X2,X1) & v11_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 1.95/0.98    inference(flattening,[],[f37])).
% 1.95/0.98  
% 1.95/0.98  fof(f48,plain,(
% 1.95/0.98    ( ! [X0,X1] : (? [X2] : (k1_waybel_9(X0,X2) != X1 & r3_waybel_9(X0,X2,X1) & v11_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (k1_waybel_9(X0,sK5) != X1 & r3_waybel_9(X0,sK5,X1) & v11_waybel_0(sK5,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(sK5,X0) & v7_waybel_0(sK5) & v4_orders_2(sK5) & ~v2_struct_0(sK5))) )),
% 1.95/0.98    introduced(choice_axiom,[])).
% 1.95/0.98  
% 1.95/0.98  fof(f47,plain,(
% 1.95/0.98    ( ! [X0] : (? [X1] : (? [X2] : (k1_waybel_9(X0,X2) != X1 & r3_waybel_9(X0,X2,X1) & v11_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_waybel_9(X0,X2) != sK4 & r3_waybel_9(X0,X2,sK4) & v11_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 1.95/0.98    introduced(choice_axiom,[])).
% 1.95/0.98  
% 1.95/0.98  fof(f46,plain,(
% 1.95/0.98    ? [X0] : (? [X1] : (? [X2] : (k1_waybel_9(X0,X2) != X1 & r3_waybel_9(X0,X2,X1) & v11_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (k1_waybel_9(sK3,X2) != X1 & r3_waybel_9(sK3,X2,X1) & v11_waybel_0(X2,sK3) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK3,X3),sK3,sK3) | ~m1_subset_1(X3,u1_struct_0(sK3))) & l1_waybel_0(X2,sK3) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_waybel_9(sK3) & v1_compts_1(sK3) & v2_lattice3(sK3) & v1_lattice3(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & v8_pre_topc(sK3) & v2_pre_topc(sK3))),
% 1.95/0.98    introduced(choice_axiom,[])).
% 1.95/0.98  
% 1.95/0.98  fof(f49,plain,(
% 1.95/0.98    ((k1_waybel_9(sK3,sK5) != sK4 & r3_waybel_9(sK3,sK5,sK4) & v11_waybel_0(sK5,sK3) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK3,X3),sK3,sK3) | ~m1_subset_1(X3,u1_struct_0(sK3))) & l1_waybel_0(sK5,sK3) & v7_waybel_0(sK5) & v4_orders_2(sK5) & ~v2_struct_0(sK5)) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_waybel_9(sK3) & v1_compts_1(sK3) & v2_lattice3(sK3) & v1_lattice3(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & v8_pre_topc(sK3) & v2_pre_topc(sK3)),
% 1.95/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f38,f48,f47,f46])).
% 1.95/0.98  
% 1.95/0.98  fof(f74,plain,(
% 1.95/0.98    v5_orders_2(sK3)),
% 1.95/0.98    inference(cnf_transformation,[],[f49])).
% 1.95/0.98  
% 1.95/0.98  fof(f78,plain,(
% 1.95/0.98    l1_waybel_9(sK3)),
% 1.95/0.98    inference(cnf_transformation,[],[f49])).
% 1.95/0.98  
% 1.95/0.98  fof(f9,axiom,(
% 1.95/0.98    ! [X0] : (l1_waybel_9(X0) => (l1_orders_2(X0) & l1_pre_topc(X0)))),
% 1.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.95/0.98  
% 1.95/0.98  fof(f16,plain,(
% 1.95/0.98    ! [X0] : (l1_waybel_9(X0) => l1_orders_2(X0))),
% 1.95/0.98    inference(pure_predicate_removal,[],[f9])).
% 1.95/0.98  
% 1.95/0.98  fof(f32,plain,(
% 1.95/0.98    ! [X0] : (l1_orders_2(X0) | ~l1_waybel_9(X0))),
% 1.95/0.98    inference(ennf_transformation,[],[f16])).
% 1.95/0.98  
% 1.95/0.98  fof(f65,plain,(
% 1.95/0.98    ( ! [X0] : (l1_orders_2(X0) | ~l1_waybel_9(X0)) )),
% 1.95/0.98    inference(cnf_transformation,[],[f32])).
% 1.95/0.98  
% 1.95/0.98  fof(f57,plain,(
% 1.95/0.98    ( ! [X2,X0,X1] : (k2_yellow_0(X0,X2) = X1 | r1_lattice3(X0,X2,sK0(X0,X1,X2)) | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 1.95/0.98    inference(cnf_transformation,[],[f40])).
% 1.95/0.98  
% 1.95/0.98  fof(f86,plain,(
% 1.95/0.98    r3_waybel_9(sK3,sK5,sK4)),
% 1.95/0.98    inference(cnf_transformation,[],[f49])).
% 1.95/0.98  
% 1.95/0.98  fof(f82,plain,(
% 1.95/0.98    v7_waybel_0(sK5)),
% 1.95/0.98    inference(cnf_transformation,[],[f49])).
% 1.95/0.98  
% 1.95/0.98  fof(f11,axiom,(
% 1.95/0.98    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) => r1_orders_2(X0,X4,X3))))))))),
% 1.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.95/0.98  
% 1.95/0.98  fof(f15,plain,(
% 1.95/0.98    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) => r1_orders_2(X0,X5,X3))))))))),
% 1.95/0.98    inference(rectify,[],[f11])).
% 1.95/0.98  
% 1.95/0.98  fof(f35,plain,(
% 1.95/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X5] : ((r1_orders_2(X0,X5,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)) | ~m1_subset_1(X5,u1_struct_0(X0))) | (~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.95/0.98    inference(ennf_transformation,[],[f15])).
% 1.95/0.98  
% 1.95/0.98  fof(f36,plain,(
% 1.95/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.95/0.98    inference(flattening,[],[f35])).
% 1.95/0.98  
% 1.95/0.98  fof(f43,plain,(
% 1.95/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | ? [X5] : (~v5_pre_topc(k4_waybel_1(X0,X5),X0,X0) & m1_subset_1(X5,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.95/0.98    inference(rectify,[],[f36])).
% 1.95/0.98  
% 1.95/0.98  fof(f44,plain,(
% 1.95/0.98    ! [X0] : (? [X5] : (~v5_pre_topc(k4_waybel_1(X0,X5),X0,X0) & m1_subset_1(X5,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0) & m1_subset_1(sK2(X0),u1_struct_0(X0))))),
% 1.95/0.98    introduced(choice_axiom,[])).
% 1.95/0.98  
% 1.95/0.98  fof(f45,plain,(
% 1.95/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | (~v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0) & m1_subset_1(sK2(X0),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.95/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).
% 1.95/0.98  
% 1.95/0.98  fof(f69,plain,(
% 1.95/0.98    ( ! [X4,X2,X0,X3,X1] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | ~v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.95/0.98    inference(cnf_transformation,[],[f45])).
% 1.95/0.98  
% 1.95/0.98  fof(f92,plain,(
% 1.95/0.98    ( ! [X4,X0,X3,X1] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | ~v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.95/0.98    inference(equality_resolution,[],[f69])).
% 1.95/0.98  
% 1.95/0.98  fof(f84,plain,(
% 1.95/0.98    ( ! [X3] : (v5_pre_topc(k4_waybel_1(sK3,X3),sK3,sK3) | ~m1_subset_1(X3,u1_struct_0(sK3))) )),
% 1.95/0.98    inference(cnf_transformation,[],[f49])).
% 1.95/0.98  
% 1.95/0.98  fof(f70,plain,(
% 1.95/0.98    v2_pre_topc(sK3)),
% 1.95/0.98    inference(cnf_transformation,[],[f49])).
% 1.95/0.98  
% 1.95/0.98  fof(f71,plain,(
% 1.95/0.98    v8_pre_topc(sK3)),
% 1.95/0.98    inference(cnf_transformation,[],[f49])).
% 1.95/0.98  
% 1.95/0.98  fof(f72,plain,(
% 1.95/0.98    v3_orders_2(sK3)),
% 1.95/0.98    inference(cnf_transformation,[],[f49])).
% 1.95/0.98  
% 1.95/0.98  fof(f73,plain,(
% 1.95/0.98    v4_orders_2(sK3)),
% 1.95/0.98    inference(cnf_transformation,[],[f49])).
% 1.95/0.98  
% 1.95/0.98  fof(f75,plain,(
% 1.95/0.98    v1_lattice3(sK3)),
% 1.95/0.98    inference(cnf_transformation,[],[f49])).
% 1.95/0.98  
% 1.95/0.98  fof(f76,plain,(
% 1.95/0.98    v2_lattice3(sK3)),
% 1.95/0.98    inference(cnf_transformation,[],[f49])).
% 1.95/0.98  
% 1.95/0.98  fof(f77,plain,(
% 1.95/0.98    v1_compts_1(sK3)),
% 1.95/0.98    inference(cnf_transformation,[],[f49])).
% 1.95/0.98  
% 1.95/0.98  fof(f80,plain,(
% 1.95/0.98    ~v2_struct_0(sK5)),
% 1.95/0.98    inference(cnf_transformation,[],[f49])).
% 1.95/0.98  
% 1.95/0.98  fof(f81,plain,(
% 1.95/0.98    v4_orders_2(sK5)),
% 1.95/0.98    inference(cnf_transformation,[],[f49])).
% 1.95/0.98  
% 1.95/0.98  fof(f83,plain,(
% 1.95/0.98    l1_waybel_0(sK5,sK3)),
% 1.95/0.98    inference(cnf_transformation,[],[f49])).
% 1.95/0.98  
% 1.95/0.98  fof(f79,plain,(
% 1.95/0.98    m1_subset_1(sK4,u1_struct_0(sK3))),
% 1.95/0.98    inference(cnf_transformation,[],[f49])).
% 1.95/0.98  
% 1.95/0.98  fof(f68,plain,(
% 1.95/0.98    ( ! [X4,X2,X0,X3,X1] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | m1_subset_1(sK2(X0),u1_struct_0(X0)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.95/0.98    inference(cnf_transformation,[],[f45])).
% 1.95/0.98  
% 1.95/0.98  fof(f93,plain,(
% 1.95/0.98    ( ! [X4,X0,X3,X1] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | m1_subset_1(sK2(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.95/0.98    inference(equality_resolution,[],[f68])).
% 1.95/0.98  
% 1.95/0.98  fof(f6,axiom,(
% 1.95/0.98    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 1.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.95/0.98  
% 1.95/0.98  fof(f17,plain,(
% 1.95/0.98    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 1.95/0.98    inference(pure_predicate_removal,[],[f6])).
% 1.95/0.98  
% 1.95/0.98  fof(f18,plain,(
% 1.95/0.98    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))))),
% 1.95/0.98    inference(pure_predicate_removal,[],[f17])).
% 1.95/0.98  
% 1.95/0.98  fof(f26,plain,(
% 1.95/0.98    ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 1.95/0.98    inference(ennf_transformation,[],[f18])).
% 1.95/0.98  
% 1.95/0.98  fof(f27,plain,(
% 1.95/0.98    ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 1.95/0.98    inference(flattening,[],[f26])).
% 1.95/0.98  
% 1.95/0.98  fof(f62,plain,(
% 1.95/0.98    ( ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 1.95/0.98    inference(cnf_transformation,[],[f27])).
% 1.95/0.98  
% 1.95/0.98  fof(f3,axiom,(
% 1.95/0.98    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 1.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.95/0.98  
% 1.95/0.98  fof(f21,plain,(
% 1.95/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 1.95/0.98    inference(ennf_transformation,[],[f3])).
% 1.95/0.98  
% 1.95/0.98  fof(f52,plain,(
% 1.95/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 1.95/0.98    inference(cnf_transformation,[],[f21])).
% 1.95/0.98  
% 1.95/0.98  fof(f2,axiom,(
% 1.95/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.95/0.98  
% 1.95/0.98  fof(f20,plain,(
% 1.95/0.98    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.95/0.98    inference(ennf_transformation,[],[f2])).
% 1.95/0.98  
% 1.95/0.98  fof(f51,plain,(
% 1.95/0.98    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.95/0.98    inference(cnf_transformation,[],[f20])).
% 1.95/0.98  
% 1.95/0.98  fof(f1,axiom,(
% 1.95/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.95/0.98  
% 1.95/0.98  fof(f19,plain,(
% 1.95/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.95/0.98    inference(ennf_transformation,[],[f1])).
% 1.95/0.98  
% 1.95/0.98  fof(f50,plain,(
% 1.95/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.95/0.98    inference(cnf_transformation,[],[f19])).
% 1.95/0.98  
% 1.95/0.98  fof(f8,axiom,(
% 1.95/0.98    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (v1_relat_1(X1) => k2_yellow_0(X0,k2_relat_1(X1)) = k5_yellow_2(X0,X1)))),
% 1.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.95/0.98  
% 1.95/0.98  fof(f30,plain,(
% 1.95/0.98    ! [X0] : (! [X1] : (k2_yellow_0(X0,k2_relat_1(X1)) = k5_yellow_2(X0,X1) | ~v1_relat_1(X1)) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 1.95/0.98    inference(ennf_transformation,[],[f8])).
% 1.95/0.98  
% 1.95/0.98  fof(f31,plain,(
% 1.95/0.98    ! [X0] : (! [X1] : (k2_yellow_0(X0,k2_relat_1(X1)) = k5_yellow_2(X0,X1) | ~v1_relat_1(X1)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 1.95/0.98    inference(flattening,[],[f30])).
% 1.95/0.98  
% 1.95/0.98  fof(f64,plain,(
% 1.95/0.98    ( ! [X0,X1] : (k2_yellow_0(X0,k2_relat_1(X1)) = k5_yellow_2(X0,X1) | ~v1_relat_1(X1) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 1.95/0.98    inference(cnf_transformation,[],[f31])).
% 1.95/0.98  
% 1.95/0.98  fof(f4,axiom,(
% 1.95/0.98    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 1.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.95/0.98  
% 1.95/0.98  fof(f22,plain,(
% 1.95/0.98    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 1.95/0.98    inference(ennf_transformation,[],[f4])).
% 1.95/0.98  
% 1.95/0.98  fof(f23,plain,(
% 1.95/0.98    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 1.95/0.98    inference(flattening,[],[f22])).
% 1.95/0.98  
% 1.95/0.98  fof(f53,plain,(
% 1.95/0.98    ( ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0)) )),
% 1.95/0.98    inference(cnf_transformation,[],[f23])).
% 1.95/0.98  
% 1.95/0.98  fof(f7,axiom,(
% 1.95/0.98    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (l1_waybel_0(X1,X0) => k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1))))),
% 1.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.95/0.98  
% 1.95/0.98  fof(f28,plain,(
% 1.95/0.98    ! [X0] : (! [X1] : (k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0)) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 1.95/0.98    inference(ennf_transformation,[],[f7])).
% 1.95/0.98  
% 1.95/0.98  fof(f29,plain,(
% 1.95/0.98    ! [X0] : (! [X1] : (k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 1.95/0.98    inference(flattening,[],[f28])).
% 1.95/0.98  
% 1.95/0.98  fof(f63,plain,(
% 1.95/0.98    ( ! [X0,X1] : (k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 1.95/0.98    inference(cnf_transformation,[],[f29])).
% 1.95/0.98  
% 1.95/0.98  fof(f58,plain,(
% 1.95/0.98    ( ! [X2,X0,X1] : (k2_yellow_0(X0,X2) = X1 | ~r1_orders_2(X0,sK0(X0,X1,X2),X1) | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 1.95/0.98    inference(cnf_transformation,[],[f40])).
% 1.95/0.98  
% 1.95/0.98  fof(f10,axiom,(
% 1.95/0.98    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & v11_waybel_0(X1,X0) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3))))))),
% 1.95/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.95/0.98  
% 1.95/0.98  fof(f33,plain,(
% 1.95/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | (~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.95/0.98    inference(ennf_transformation,[],[f10])).
% 1.95/0.98  
% 1.95/0.98  fof(f34,plain,(
% 1.95/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.95/0.98    inference(flattening,[],[f33])).
% 1.95/0.98  
% 1.95/0.98  fof(f41,plain,(
% 1.95/0.98    ! [X0] : (? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0) & m1_subset_1(sK1(X0),u1_struct_0(X0))))),
% 1.95/0.98    introduced(choice_axiom,[])).
% 1.95/0.98  
% 1.95/0.98  fof(f42,plain,(
% 1.95/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | (~v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0) & m1_subset_1(sK1(X0),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.95/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f41])).
% 1.95/0.98  
% 1.95/0.98  fof(f67,plain,(
% 1.95/0.98    ( ! [X2,X0,X3,X1] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.95/0.98    inference(cnf_transformation,[],[f42])).
% 1.95/0.98  
% 1.95/0.98  fof(f90,plain,(
% 1.95/0.98    ( ! [X0,X3,X1] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v11_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.95/0.98    inference(equality_resolution,[],[f67])).
% 1.95/0.98  
% 1.95/0.98  fof(f85,plain,(
% 1.95/0.98    v11_waybel_0(sK5,sK3)),
% 1.95/0.98    inference(cnf_transformation,[],[f49])).
% 1.95/0.98  
% 1.95/0.98  fof(f66,plain,(
% 1.95/0.98    ( ! [X2,X0,X3,X1] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | m1_subset_1(sK1(X0),u1_struct_0(X0)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.95/0.98    inference(cnf_transformation,[],[f42])).
% 1.95/0.98  
% 1.95/0.98  fof(f91,plain,(
% 1.95/0.98    ( ! [X0,X3,X1] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v11_waybel_0(X1,X0) | m1_subset_1(sK1(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.95/0.98    inference(equality_resolution,[],[f66])).
% 1.95/0.98  
% 1.95/0.98  fof(f87,plain,(
% 1.95/0.98    k1_waybel_9(sK3,sK5) != sK4),
% 1.95/0.98    inference(cnf_transformation,[],[f49])).
% 1.95/0.98  
% 1.95/0.98  cnf(c_9,plain,
% 1.95/0.98      ( ~ r1_lattice3(X0,X1,X2)
% 1.95/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.95/0.98      | m1_subset_1(sK0(X0,X2,X1),u1_struct_0(X0))
% 1.95/0.98      | ~ v5_orders_2(X0)
% 1.95/0.98      | ~ l1_orders_2(X0)
% 1.95/0.98      | k2_yellow_0(X0,X1) = X2 ),
% 1.95/0.98      inference(cnf_transformation,[],[f56]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_33,negated_conjecture,
% 1.95/0.98      ( v5_orders_2(sK3) ),
% 1.95/0.98      inference(cnf_transformation,[],[f74]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_982,plain,
% 1.95/0.98      ( ~ r1_lattice3(X0,X1,X2)
% 1.95/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.95/0.98      | m1_subset_1(sK0(X0,X2,X1),u1_struct_0(X0))
% 1.95/0.98      | ~ l1_orders_2(X0)
% 1.95/0.98      | k2_yellow_0(X0,X1) = X2
% 1.95/0.98      | sK3 != X0 ),
% 1.95/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_33]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_983,plain,
% 1.95/0.98      ( ~ r1_lattice3(sK3,X0,X1)
% 1.95/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.95/0.98      | m1_subset_1(sK0(sK3,X1,X0),u1_struct_0(sK3))
% 1.95/0.98      | ~ l1_orders_2(sK3)
% 1.95/0.98      | k2_yellow_0(sK3,X0) = X1 ),
% 1.95/0.98      inference(unflattening,[status(thm)],[c_982]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_29,negated_conjecture,
% 1.95/0.98      ( l1_waybel_9(sK3) ),
% 1.95/0.98      inference(cnf_transformation,[],[f78]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_15,plain,
% 1.95/0.98      ( ~ l1_waybel_9(X0) | l1_orders_2(X0) ),
% 1.95/0.98      inference(cnf_transformation,[],[f65]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_70,plain,
% 1.95/0.98      ( ~ l1_waybel_9(sK3) | l1_orders_2(sK3) ),
% 1.95/0.98      inference(instantiation,[status(thm)],[c_15]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_987,plain,
% 1.95/0.98      ( m1_subset_1(sK0(sK3,X1,X0),u1_struct_0(sK3))
% 1.95/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.95/0.98      | ~ r1_lattice3(sK3,X0,X1)
% 1.95/0.98      | k2_yellow_0(sK3,X0) = X1 ),
% 1.95/0.98      inference(global_propositional_subsumption,
% 1.95/0.98                [status(thm)],
% 1.95/0.98                [c_983,c_29,c_70]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_988,plain,
% 1.95/0.98      ( ~ r1_lattice3(sK3,X0,X1)
% 1.95/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.95/0.98      | m1_subset_1(sK0(sK3,X1,X0),u1_struct_0(sK3))
% 1.95/0.98      | k2_yellow_0(sK3,X0) = X1 ),
% 1.95/0.98      inference(renaming,[status(thm)],[c_987]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_2081,plain,
% 1.95/0.98      ( ~ r1_lattice3(sK3,X0_68,X0_66)
% 1.95/0.98      | ~ m1_subset_1(X0_66,u1_struct_0(sK3))
% 1.95/0.98      | m1_subset_1(sK0(sK3,X0_66,X0_68),u1_struct_0(sK3))
% 1.95/0.98      | k2_yellow_0(sK3,X0_68) = X0_66 ),
% 1.95/0.98      inference(subtyping,[status(esa)],[c_988]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_2535,plain,
% 1.95/0.98      ( k2_yellow_0(sK3,X0_68) = X0_66
% 1.95/0.98      | r1_lattice3(sK3,X0_68,X0_66) != iProver_top
% 1.95/0.98      | m1_subset_1(X0_66,u1_struct_0(sK3)) != iProver_top
% 1.95/0.98      | m1_subset_1(sK0(sK3,X0_66,X0_68),u1_struct_0(sK3)) = iProver_top ),
% 1.95/0.98      inference(predicate_to_equality,[status(thm)],[c_2081]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_8,plain,
% 1.95/0.98      ( ~ r1_lattice3(X0,X1,X2)
% 1.95/0.98      | r1_lattice3(X0,X1,sK0(X0,X2,X1))
% 1.95/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.95/0.98      | ~ v5_orders_2(X0)
% 1.95/0.98      | ~ l1_orders_2(X0)
% 1.95/0.98      | k2_yellow_0(X0,X1) = X2 ),
% 1.95/0.98      inference(cnf_transformation,[],[f57]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_1006,plain,
% 1.95/0.98      ( ~ r1_lattice3(X0,X1,X2)
% 1.95/0.98      | r1_lattice3(X0,X1,sK0(X0,X2,X1))
% 1.95/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.95/0.98      | ~ l1_orders_2(X0)
% 1.95/0.98      | k2_yellow_0(X0,X1) = X2
% 1.95/0.98      | sK3 != X0 ),
% 1.95/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_33]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_1007,plain,
% 1.95/0.98      ( ~ r1_lattice3(sK3,X0,X1)
% 1.95/0.98      | r1_lattice3(sK3,X0,sK0(sK3,X1,X0))
% 1.95/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.95/0.98      | ~ l1_orders_2(sK3)
% 1.95/0.98      | k2_yellow_0(sK3,X0) = X1 ),
% 1.95/0.98      inference(unflattening,[status(thm)],[c_1006]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_1011,plain,
% 1.95/0.98      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.95/0.98      | r1_lattice3(sK3,X0,sK0(sK3,X1,X0))
% 1.95/0.98      | ~ r1_lattice3(sK3,X0,X1)
% 1.95/0.98      | k2_yellow_0(sK3,X0) = X1 ),
% 1.95/0.98      inference(global_propositional_subsumption,
% 1.95/0.98                [status(thm)],
% 1.95/0.98                [c_1007,c_29,c_70]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_1012,plain,
% 1.95/0.98      ( ~ r1_lattice3(sK3,X0,X1)
% 1.95/0.98      | r1_lattice3(sK3,X0,sK0(sK3,X1,X0))
% 1.95/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.95/0.98      | k2_yellow_0(sK3,X0) = X1 ),
% 1.95/0.98      inference(renaming,[status(thm)],[c_1011]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_2080,plain,
% 1.95/0.98      ( ~ r1_lattice3(sK3,X0_68,X0_66)
% 1.95/0.98      | r1_lattice3(sK3,X0_68,sK0(sK3,X0_66,X0_68))
% 1.95/0.98      | ~ m1_subset_1(X0_66,u1_struct_0(sK3))
% 1.95/0.98      | k2_yellow_0(sK3,X0_68) = X0_66 ),
% 1.95/0.98      inference(subtyping,[status(esa)],[c_1012]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_2536,plain,
% 1.95/0.98      ( k2_yellow_0(sK3,X0_68) = X0_66
% 1.95/0.98      | r1_lattice3(sK3,X0_68,X0_66) != iProver_top
% 1.95/0.98      | r1_lattice3(sK3,X0_68,sK0(sK3,X0_66,X0_68)) = iProver_top
% 1.95/0.98      | m1_subset_1(X0_66,u1_struct_0(sK3)) != iProver_top ),
% 1.95/0.98      inference(predicate_to_equality,[status(thm)],[c_2080]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_21,negated_conjecture,
% 1.95/0.98      ( r3_waybel_9(sK3,sK5,sK4) ),
% 1.95/0.98      inference(cnf_transformation,[],[f86]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_25,negated_conjecture,
% 1.95/0.98      ( v7_waybel_0(sK5) ),
% 1.95/0.98      inference(cnf_transformation,[],[f82]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_18,plain,
% 1.95/0.98      ( ~ v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0)
% 1.95/0.98      | ~ r3_waybel_9(X0,X1,X2)
% 1.95/0.98      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 1.95/0.98      | r1_orders_2(X0,X3,X2)
% 1.95/0.98      | ~ l1_waybel_0(X1,X0)
% 1.95/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.95/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.95/0.98      | ~ v2_pre_topc(X0)
% 1.95/0.98      | ~ v8_pre_topc(X0)
% 1.95/0.98      | ~ v3_orders_2(X0)
% 1.95/0.98      | ~ v1_lattice3(X0)
% 1.95/0.98      | ~ v1_compts_1(X0)
% 1.95/0.98      | ~ v4_orders_2(X1)
% 1.95/0.98      | ~ v4_orders_2(X0)
% 1.95/0.98      | ~ v7_waybel_0(X1)
% 1.95/0.98      | ~ l1_waybel_9(X0)
% 1.95/0.98      | ~ v5_orders_2(X0)
% 1.95/0.98      | ~ v2_lattice3(X0)
% 1.95/0.98      | v2_struct_0(X1) ),
% 1.95/0.98      inference(cnf_transformation,[],[f92]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_23,negated_conjecture,
% 1.95/0.98      ( v5_pre_topc(k4_waybel_1(sK3,X0),sK3,sK3)
% 1.95/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 1.95/0.98      inference(cnf_transformation,[],[f84]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_509,plain,
% 1.95/0.98      ( ~ r3_waybel_9(X0,X1,X2)
% 1.95/0.98      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 1.95/0.98      | r1_orders_2(X0,X3,X2)
% 1.95/0.98      | ~ l1_waybel_0(X1,X0)
% 1.95/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.95/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.95/0.98      | ~ m1_subset_1(X4,u1_struct_0(sK3))
% 1.95/0.98      | ~ v2_pre_topc(X0)
% 1.95/0.98      | ~ v8_pre_topc(X0)
% 1.95/0.98      | ~ v3_orders_2(X0)
% 1.95/0.98      | ~ v1_lattice3(X0)
% 1.95/0.98      | ~ v1_compts_1(X0)
% 1.95/0.98      | ~ v4_orders_2(X1)
% 1.95/0.98      | ~ v4_orders_2(X0)
% 1.95/0.98      | ~ v7_waybel_0(X1)
% 1.95/0.98      | ~ l1_waybel_9(X0)
% 1.95/0.98      | ~ v5_orders_2(X0)
% 1.95/0.98      | ~ v2_lattice3(X0)
% 1.95/0.98      | v2_struct_0(X1)
% 1.95/0.98      | k4_waybel_1(X0,sK2(X0)) != k4_waybel_1(sK3,X4)
% 1.95/0.98      | sK3 != X0 ),
% 1.95/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_23]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_510,plain,
% 1.95/0.98      ( ~ r3_waybel_9(sK3,X0,X1)
% 1.95/0.98      | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
% 1.95/0.98      | r1_orders_2(sK3,X2,X1)
% 1.95/0.98      | ~ l1_waybel_0(X0,sK3)
% 1.95/0.98      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 1.95/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.95/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.95/0.98      | ~ v2_pre_topc(sK3)
% 1.95/0.98      | ~ v8_pre_topc(sK3)
% 1.95/0.98      | ~ v3_orders_2(sK3)
% 1.95/0.98      | ~ v1_lattice3(sK3)
% 1.95/0.98      | ~ v1_compts_1(sK3)
% 1.95/0.98      | ~ v4_orders_2(X0)
% 1.95/0.98      | ~ v4_orders_2(sK3)
% 1.95/0.98      | ~ v7_waybel_0(X0)
% 1.95/0.98      | ~ l1_waybel_9(sK3)
% 1.95/0.98      | ~ v5_orders_2(sK3)
% 1.95/0.98      | ~ v2_lattice3(sK3)
% 1.95/0.98      | v2_struct_0(X0)
% 1.95/0.98      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X3) ),
% 1.95/0.98      inference(unflattening,[status(thm)],[c_509]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_37,negated_conjecture,
% 1.95/0.98      ( v2_pre_topc(sK3) ),
% 1.95/0.98      inference(cnf_transformation,[],[f70]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_36,negated_conjecture,
% 1.95/0.98      ( v8_pre_topc(sK3) ),
% 1.95/0.98      inference(cnf_transformation,[],[f71]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_35,negated_conjecture,
% 1.95/0.98      ( v3_orders_2(sK3) ),
% 1.95/0.98      inference(cnf_transformation,[],[f72]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_34,negated_conjecture,
% 1.95/0.98      ( v4_orders_2(sK3) ),
% 1.95/0.98      inference(cnf_transformation,[],[f73]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_32,negated_conjecture,
% 1.95/0.98      ( v1_lattice3(sK3) ),
% 1.95/0.98      inference(cnf_transformation,[],[f75]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_31,negated_conjecture,
% 1.95/0.98      ( v2_lattice3(sK3) ),
% 1.95/0.98      inference(cnf_transformation,[],[f76]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_30,negated_conjecture,
% 1.95/0.98      ( v1_compts_1(sK3) ),
% 1.95/0.98      inference(cnf_transformation,[],[f77]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_514,plain,
% 1.95/0.98      ( ~ v7_waybel_0(X0)
% 1.95/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.95/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.95/0.98      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 1.95/0.98      | ~ l1_waybel_0(X0,sK3)
% 1.95/0.98      | r1_orders_2(sK3,X2,X1)
% 1.95/0.98      | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
% 1.95/0.98      | ~ r3_waybel_9(sK3,X0,X1)
% 1.95/0.98      | ~ v4_orders_2(X0)
% 1.95/0.98      | v2_struct_0(X0)
% 1.95/0.98      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X3) ),
% 1.95/0.98      inference(global_propositional_subsumption,
% 1.95/0.98                [status(thm)],
% 1.95/0.98                [c_510,c_37,c_36,c_35,c_34,c_33,c_32,c_31,c_30,c_29]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_515,plain,
% 1.95/0.98      ( ~ r3_waybel_9(sK3,X0,X1)
% 1.95/0.98      | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
% 1.95/0.98      | r1_orders_2(sK3,X2,X1)
% 1.95/0.98      | ~ l1_waybel_0(X0,sK3)
% 1.95/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.95/0.98      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 1.95/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.95/0.98      | ~ v4_orders_2(X0)
% 1.95/0.98      | ~ v7_waybel_0(X0)
% 1.95/0.98      | v2_struct_0(X0)
% 1.95/0.98      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X3) ),
% 1.95/0.98      inference(renaming,[status(thm)],[c_514]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_690,plain,
% 1.95/0.98      ( ~ r3_waybel_9(sK3,X0,X1)
% 1.95/0.98      | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
% 1.95/0.98      | r1_orders_2(sK3,X2,X1)
% 1.95/0.98      | ~ l1_waybel_0(X0,sK3)
% 1.95/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.95/0.98      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 1.95/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.95/0.98      | ~ v4_orders_2(X0)
% 1.95/0.98      | v2_struct_0(X0)
% 1.95/0.98      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X3)
% 1.95/0.98      | sK5 != X0 ),
% 1.95/0.98      inference(resolution_lifted,[status(thm)],[c_25,c_515]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_691,plain,
% 1.95/0.98      ( ~ r3_waybel_9(sK3,sK5,X0)
% 1.95/0.98      | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
% 1.95/0.98      | r1_orders_2(sK3,X1,X0)
% 1.95/0.98      | ~ l1_waybel_0(sK5,sK3)
% 1.95/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.95/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.95/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.95/0.98      | ~ v4_orders_2(sK5)
% 1.95/0.98      | v2_struct_0(sK5)
% 1.95/0.98      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X2) ),
% 1.95/0.98      inference(unflattening,[status(thm)],[c_690]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_27,negated_conjecture,
% 1.95/0.98      ( ~ v2_struct_0(sK5) ),
% 1.95/0.98      inference(cnf_transformation,[],[f80]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_26,negated_conjecture,
% 1.95/0.98      ( v4_orders_2(sK5) ),
% 1.95/0.98      inference(cnf_transformation,[],[f81]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_24,negated_conjecture,
% 1.95/0.98      ( l1_waybel_0(sK5,sK3) ),
% 1.95/0.98      inference(cnf_transformation,[],[f83]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_695,plain,
% 1.95/0.98      ( r1_orders_2(sK3,X1,X0)
% 1.95/0.98      | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
% 1.95/0.98      | ~ r3_waybel_9(sK3,sK5,X0)
% 1.95/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.95/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.95/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.95/0.98      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X2) ),
% 1.95/0.98      inference(global_propositional_subsumption,
% 1.95/0.98                [status(thm)],
% 1.95/0.98                [c_691,c_27,c_26,c_24]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_696,plain,
% 1.95/0.98      ( ~ r3_waybel_9(sK3,sK5,X0)
% 1.95/0.98      | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
% 1.95/0.98      | r1_orders_2(sK3,X1,X0)
% 1.95/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.95/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.95/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.95/0.98      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X2) ),
% 1.95/0.98      inference(renaming,[status(thm)],[c_695]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_830,plain,
% 1.95/0.98      ( ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.95/0.98      | r1_orders_2(sK3,X0,X1)
% 1.95/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.95/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.95/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.95/0.98      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X2)
% 1.95/0.98      | sK4 != X1
% 1.95/0.98      | sK5 != sK5
% 1.95/0.98      | sK3 != sK3 ),
% 1.95/0.98      inference(resolution_lifted,[status(thm)],[c_21,c_696]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_831,plain,
% 1.95/0.98      ( ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.95/0.98      | r1_orders_2(sK3,X0,sK4)
% 1.95/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.95/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.95/0.98      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 1.95/0.98      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1) ),
% 1.95/0.98      inference(unflattening,[status(thm)],[c_830]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_28,negated_conjecture,
% 1.95/0.98      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 1.95/0.98      inference(cnf_transformation,[],[f79]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_835,plain,
% 1.95/0.98      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.95/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.95/0.98      | r1_orders_2(sK3,X0,sK4)
% 1.95/0.98      | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.95/0.98      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1) ),
% 1.95/0.98      inference(global_propositional_subsumption,
% 1.95/0.98                [status(thm)],
% 1.95/0.98                [c_831,c_28]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_836,plain,
% 1.95/0.98      ( ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.95/0.98      | r1_orders_2(sK3,X0,sK4)
% 1.95/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.95/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.95/0.98      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1) ),
% 1.95/0.98      inference(renaming,[status(thm)],[c_835]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_2087,plain,
% 1.95/0.98      ( ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_66)
% 1.95/0.98      | r1_orders_2(sK3,X0_66,sK4)
% 1.95/0.98      | ~ m1_subset_1(X1_66,u1_struct_0(sK3))
% 1.95/0.98      | ~ m1_subset_1(X0_66,u1_struct_0(sK3))
% 1.95/0.98      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1_66) ),
% 1.95/0.98      inference(subtyping,[status(esa)],[c_836]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_2096,plain,
% 1.95/0.98      ( ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_66)
% 1.95/0.98      | r1_orders_2(sK3,X0_66,sK4)
% 1.95/0.98      | ~ m1_subset_1(X0_66,u1_struct_0(sK3))
% 1.95/0.98      | ~ sP1_iProver_split ),
% 1.95/0.98      inference(splitting,
% 1.95/0.98                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 1.95/0.98                [c_2087]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_2528,plain,
% 1.95/0.98      ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_66) != iProver_top
% 1.95/0.98      | r1_orders_2(sK3,X0_66,sK4) = iProver_top
% 1.95/0.98      | m1_subset_1(X0_66,u1_struct_0(sK3)) != iProver_top
% 1.95/0.98      | sP1_iProver_split != iProver_top ),
% 1.95/0.98      inference(predicate_to_equality,[status(thm)],[c_2096]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_2097,plain,
% 1.95/0.98      ( sP1_iProver_split | sP0_iProver_split ),
% 1.95/0.98      inference(splitting,
% 1.95/0.98                [splitting(split),new_symbols(definition,[])],
% 1.95/0.98                [c_2087]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_2159,plain,
% 1.95/0.98      ( sP1_iProver_split = iProver_top
% 1.95/0.98      | sP0_iProver_split = iProver_top ),
% 1.95/0.98      inference(predicate_to_equality,[status(thm)],[c_2097]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_2160,plain,
% 1.95/0.98      ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_66) != iProver_top
% 1.95/0.98      | r1_orders_2(sK3,X0_66,sK4) = iProver_top
% 1.95/0.98      | m1_subset_1(X0_66,u1_struct_0(sK3)) != iProver_top
% 1.95/0.98      | sP1_iProver_split != iProver_top ),
% 1.95/0.98      inference(predicate_to_equality,[status(thm)],[c_2096]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_19,plain,
% 1.95/0.98      ( ~ r3_waybel_9(X0,X1,X2)
% 1.95/0.98      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 1.95/0.98      | r1_orders_2(X0,X3,X2)
% 1.95/0.98      | ~ l1_waybel_0(X1,X0)
% 1.95/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.95/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.95/0.98      | m1_subset_1(sK2(X0),u1_struct_0(X0))
% 1.95/0.98      | ~ v2_pre_topc(X0)
% 1.95/0.98      | ~ v8_pre_topc(X0)
% 1.95/0.98      | ~ v3_orders_2(X0)
% 1.95/0.98      | ~ v1_lattice3(X0)
% 1.95/0.98      | ~ v1_compts_1(X0)
% 1.95/0.98      | ~ v4_orders_2(X1)
% 1.95/0.98      | ~ v4_orders_2(X0)
% 1.95/0.98      | ~ v7_waybel_0(X1)
% 1.95/0.98      | ~ l1_waybel_9(X0)
% 1.95/0.98      | ~ v5_orders_2(X0)
% 1.95/0.98      | ~ v2_lattice3(X0)
% 1.95/0.98      | v2_struct_0(X1) ),
% 1.95/0.98      inference(cnf_transformation,[],[f93]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_585,plain,
% 1.95/0.98      ( ~ r3_waybel_9(X0,X1,X2)
% 1.95/0.98      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 1.95/0.98      | r1_orders_2(X0,X3,X2)
% 1.95/0.98      | ~ l1_waybel_0(X1,X0)
% 1.95/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.95/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.95/0.98      | m1_subset_1(sK2(X0),u1_struct_0(X0))
% 1.95/0.98      | ~ v2_pre_topc(X0)
% 1.95/0.98      | ~ v8_pre_topc(X0)
% 1.95/0.98      | ~ v3_orders_2(X0)
% 1.95/0.98      | ~ v1_lattice3(X0)
% 1.95/0.98      | ~ v4_orders_2(X1)
% 1.95/0.98      | ~ v4_orders_2(X0)
% 1.95/0.98      | ~ v7_waybel_0(X1)
% 1.95/0.98      | ~ l1_waybel_9(X0)
% 1.95/0.98      | ~ v5_orders_2(X0)
% 1.95/0.98      | ~ v2_lattice3(X0)
% 1.95/0.98      | v2_struct_0(X1)
% 1.95/0.98      | sK3 != X0 ),
% 1.95/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_586,plain,
% 1.95/0.98      ( ~ r3_waybel_9(sK3,X0,X1)
% 1.95/0.98      | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
% 1.95/0.98      | r1_orders_2(sK3,X2,X1)
% 1.95/0.98      | ~ l1_waybel_0(X0,sK3)
% 1.95/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.95/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.95/0.98      | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
% 1.95/0.98      | ~ v2_pre_topc(sK3)
% 1.95/0.98      | ~ v8_pre_topc(sK3)
% 1.95/0.98      | ~ v3_orders_2(sK3)
% 1.95/0.98      | ~ v1_lattice3(sK3)
% 1.95/0.98      | ~ v4_orders_2(X0)
% 1.95/0.98      | ~ v4_orders_2(sK3)
% 1.95/0.98      | ~ v7_waybel_0(X0)
% 1.95/0.98      | ~ l1_waybel_9(sK3)
% 1.95/0.98      | ~ v5_orders_2(sK3)
% 1.95/0.98      | ~ v2_lattice3(sK3)
% 1.95/0.98      | v2_struct_0(X0) ),
% 1.95/0.98      inference(unflattening,[status(thm)],[c_585]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_590,plain,
% 1.95/0.98      ( ~ v7_waybel_0(X0)
% 1.95/0.98      | ~ r3_waybel_9(sK3,X0,X1)
% 1.95/0.98      | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
% 1.95/0.98      | r1_orders_2(sK3,X2,X1)
% 1.95/0.98      | ~ l1_waybel_0(X0,sK3)
% 1.95/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.95/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.95/0.98      | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
% 1.95/0.98      | ~ v4_orders_2(X0)
% 1.95/0.98      | v2_struct_0(X0) ),
% 1.95/0.98      inference(global_propositional_subsumption,
% 1.95/0.98                [status(thm)],
% 1.95/0.98                [c_586,c_37,c_36,c_35,c_34,c_33,c_32,c_31,c_29]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_591,plain,
% 1.95/0.98      ( ~ r3_waybel_9(sK3,X0,X1)
% 1.95/0.98      | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
% 1.95/0.98      | r1_orders_2(sK3,X2,X1)
% 1.95/0.98      | ~ l1_waybel_0(X0,sK3)
% 1.95/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.95/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.95/0.98      | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
% 1.95/0.98      | ~ v4_orders_2(X0)
% 1.95/0.98      | ~ v7_waybel_0(X0)
% 1.95/0.98      | v2_struct_0(X0) ),
% 1.95/0.98      inference(renaming,[status(thm)],[c_590]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_660,plain,
% 1.95/0.98      ( ~ r3_waybel_9(sK3,X0,X1)
% 1.95/0.98      | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
% 1.95/0.98      | r1_orders_2(sK3,X2,X1)
% 1.95/0.98      | ~ l1_waybel_0(X0,sK3)
% 1.95/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.95/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.95/0.98      | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
% 1.95/0.98      | ~ v4_orders_2(X0)
% 1.95/0.98      | v2_struct_0(X0)
% 1.95/0.98      | sK5 != X0 ),
% 1.95/0.98      inference(resolution_lifted,[status(thm)],[c_25,c_591]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_661,plain,
% 1.95/0.98      ( ~ r3_waybel_9(sK3,sK5,X0)
% 1.95/0.98      | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
% 1.95/0.98      | r1_orders_2(sK3,X1,X0)
% 1.95/0.98      | ~ l1_waybel_0(sK5,sK3)
% 1.95/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.95/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.95/0.98      | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
% 1.95/0.98      | ~ v4_orders_2(sK5)
% 1.95/0.98      | v2_struct_0(sK5) ),
% 1.95/0.98      inference(unflattening,[status(thm)],[c_660]) ).
% 1.95/0.98  
% 1.95/0.98  cnf(c_665,plain,
% 1.95/0.98      ( r1_orders_2(sK3,X1,X0)
% 1.95/0.98      | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
% 1.95/0.98      | ~ r3_waybel_9(sK3,sK5,X0)
% 1.95/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.95/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.95/0.98      | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) ),
% 1.95/0.98      inference(global_propositional_subsumption,
% 1.95/0.98                [status(thm)],
% 1.95/0.98                [c_661,c_27,c_26,c_24]) ).
% 1.95/0.98  
% 1.95/0.99  cnf(c_666,plain,
% 1.95/0.99      ( ~ r3_waybel_9(sK3,sK5,X0)
% 1.95/0.99      | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
% 1.95/0.99      | r1_orders_2(sK3,X1,X0)
% 1.95/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.95/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.95/0.99      | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) ),
% 1.95/0.99      inference(renaming,[status(thm)],[c_665]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_857,plain,
% 1.95/0.99      ( ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.95/0.99      | r1_orders_2(sK3,X0,X1)
% 1.95/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.95/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.95/0.99      | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
% 1.95/0.99      | sK4 != X1
% 1.95/0.99      | sK5 != sK5
% 1.95/0.99      | sK3 != sK3 ),
% 1.95/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_666]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_858,plain,
% 1.95/0.99      ( ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.95/0.99      | r1_orders_2(sK3,X0,sK4)
% 1.95/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.95/0.99      | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
% 1.95/0.99      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 1.95/0.99      inference(unflattening,[status(thm)],[c_857]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_862,plain,
% 1.95/0.99      ( m1_subset_1(sK2(sK3),u1_struct_0(sK3))
% 1.95/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.95/0.99      | r1_orders_2(sK3,X0,sK4)
% 1.95/0.99      | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0) ),
% 1.95/0.99      inference(global_propositional_subsumption,
% 1.95/0.99                [status(thm)],
% 1.95/0.99                [c_858,c_28]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_863,plain,
% 1.95/0.99      ( ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.95/0.99      | r1_orders_2(sK3,X0,sK4)
% 1.95/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.95/0.99      | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) ),
% 1.95/0.99      inference(renaming,[status(thm)],[c_862]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2086,plain,
% 1.95/0.99      ( ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_66)
% 1.95/0.99      | r1_orders_2(sK3,X0_66,sK4)
% 1.95/0.99      | ~ m1_subset_1(X0_66,u1_struct_0(sK3))
% 1.95/0.99      | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) ),
% 1.95/0.99      inference(subtyping,[status(esa)],[c_863]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2166,plain,
% 1.95/0.99      ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_66) != iProver_top
% 1.95/0.99      | r1_orders_2(sK3,X0_66,sK4) = iProver_top
% 1.95/0.99      | m1_subset_1(X0_66,u1_struct_0(sK3)) != iProver_top
% 1.95/0.99      | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_2086]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2095,plain,
% 1.95/0.99      ( ~ m1_subset_1(X0_66,u1_struct_0(sK3))
% 1.95/0.99      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X0_66)
% 1.95/0.99      | ~ sP0_iProver_split ),
% 1.95/0.99      inference(splitting,
% 1.95/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.95/0.99                [c_2087]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2529,plain,
% 1.95/0.99      ( k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X0_66)
% 1.95/0.99      | m1_subset_1(X0_66,u1_struct_0(sK3)) != iProver_top
% 1.95/0.99      | sP0_iProver_split != iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_2095]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2729,plain,
% 1.95/0.99      ( m1_subset_1(sK2(sK3),u1_struct_0(sK3)) != iProver_top
% 1.95/0.99      | sP0_iProver_split != iProver_top ),
% 1.95/0.99      inference(equality_resolution,[status(thm)],[c_2529]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2943,plain,
% 1.95/0.99      ( m1_subset_1(X0_66,u1_struct_0(sK3)) != iProver_top
% 1.95/0.99      | r1_orders_2(sK3,X0_66,sK4) = iProver_top
% 1.95/0.99      | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_66) != iProver_top ),
% 1.95/0.99      inference(global_propositional_subsumption,
% 1.95/0.99                [status(thm)],
% 1.95/0.99                [c_2528,c_2159,c_2160,c_2166,c_2729]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2944,plain,
% 1.95/0.99      ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_66) != iProver_top
% 1.95/0.99      | r1_orders_2(sK3,X0_66,sK4) = iProver_top
% 1.95/0.99      | m1_subset_1(X0_66,u1_struct_0(sK3)) != iProver_top ),
% 1.95/0.99      inference(renaming,[status(thm)],[c_2943]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_12,plain,
% 1.95/0.99      ( ~ l1_waybel_0(X0,X1)
% 1.95/0.99      | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.95/0.99      | ~ l1_struct_0(X1) ),
% 1.95/0.99      inference(cnf_transformation,[],[f62]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2,plain,
% 1.95/0.99      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 1.95/0.99      inference(cnf_transformation,[],[f52]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_410,plain,
% 1.95/0.99      ( ~ l1_waybel_0(X0,X1)
% 1.95/0.99      | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.95/0.99      | ~ l1_orders_2(X2)
% 1.95/0.99      | X2 != X1 ),
% 1.95/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_2]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_411,plain,
% 1.95/0.99      ( ~ l1_waybel_0(X0,X1)
% 1.95/0.99      | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.95/0.99      | ~ l1_orders_2(X1) ),
% 1.95/0.99      inference(unflattening,[status(thm)],[c_410]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_738,plain,
% 1.95/0.99      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
% 1.95/0.99      | ~ l1_orders_2(X0)
% 1.95/0.99      | sK5 != X1
% 1.95/0.99      | sK3 != X0 ),
% 1.95/0.99      inference(resolution_lifted,[status(thm)],[c_411,c_24]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_739,plain,
% 1.95/0.99      ( m1_subset_1(u1_waybel_0(sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 1.95/0.99      | ~ l1_orders_2(sK3) ),
% 1.95/0.99      inference(unflattening,[status(thm)],[c_738]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_741,plain,
% 1.95/0.99      ( m1_subset_1(u1_waybel_0(sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 1.95/0.99      inference(global_propositional_subsumption,
% 1.95/0.99                [status(thm)],
% 1.95/0.99                [c_739,c_29,c_70]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2090,plain,
% 1.95/0.99      ( m1_subset_1(u1_waybel_0(sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 1.95/0.99      inference(subtyping,[status(esa)],[c_741]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2525,plain,
% 1.95/0.99      ( m1_subset_1(u1_waybel_0(sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_2090]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_1,plain,
% 1.95/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.95/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 1.95/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2093,plain,
% 1.95/0.99      ( ~ m1_subset_1(X0_66,k1_zfmisc_1(k2_zfmisc_1(X0_69,X1_69)))
% 1.95/0.99      | k2_relset_1(X0_69,X1_69,X0_66) = k2_relat_1(X0_66) ),
% 1.95/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2523,plain,
% 1.95/0.99      ( k2_relset_1(X0_69,X1_69,X0_66) = k2_relat_1(X0_66)
% 1.95/0.99      | m1_subset_1(X0_66,k1_zfmisc_1(k2_zfmisc_1(X0_69,X1_69))) != iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_2093]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2785,plain,
% 1.95/0.99      ( k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)) = k2_relat_1(u1_waybel_0(sK3,sK5)) ),
% 1.95/0.99      inference(superposition,[status(thm)],[c_2525,c_2523]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2949,plain,
% 1.95/0.99      ( r1_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_66) != iProver_top
% 1.95/0.99      | r1_orders_2(sK3,X0_66,sK4) = iProver_top
% 1.95/0.99      | m1_subset_1(X0_66,u1_struct_0(sK3)) != iProver_top ),
% 1.95/0.99      inference(light_normalisation,[status(thm)],[c_2944,c_2785]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3059,plain,
% 1.95/0.99      ( k2_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = X0_66
% 1.95/0.99      | r1_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_66) != iProver_top
% 1.95/0.99      | r1_orders_2(sK3,sK0(sK3,X0_66,k2_relat_1(u1_waybel_0(sK3,sK5))),sK4) = iProver_top
% 1.95/0.99      | m1_subset_1(X0_66,u1_struct_0(sK3)) != iProver_top
% 1.95/0.99      | m1_subset_1(sK0(sK3,X0_66,k2_relat_1(u1_waybel_0(sK3,sK5))),u1_struct_0(sK3)) != iProver_top ),
% 1.95/0.99      inference(superposition,[status(thm)],[c_2536,c_2949]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_0,plain,
% 1.95/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.95/0.99      | v1_relat_1(X0) ),
% 1.95/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2094,plain,
% 1.95/0.99      ( ~ m1_subset_1(X0_66,k1_zfmisc_1(k2_zfmisc_1(X0_69,X1_69)))
% 1.95/0.99      | v1_relat_1(X0_66) ),
% 1.95/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2522,plain,
% 1.95/0.99      ( m1_subset_1(X0_66,k1_zfmisc_1(k2_zfmisc_1(X0_69,X1_69))) != iProver_top
% 1.95/0.99      | v1_relat_1(X0_66) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_2094]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2780,plain,
% 1.95/0.99      ( v1_relat_1(u1_waybel_0(sK3,sK5)) = iProver_top ),
% 1.95/0.99      inference(superposition,[status(thm)],[c_2525,c_2522]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_14,plain,
% 1.95/0.99      ( v2_struct_0(X0)
% 1.95/0.99      | ~ l1_orders_2(X0)
% 1.95/0.99      | ~ v1_relat_1(X1)
% 1.95/0.99      | k2_yellow_0(X0,k2_relat_1(X1)) = k5_yellow_2(X0,X1) ),
% 1.95/0.99      inference(cnf_transformation,[],[f64]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3,plain,
% 1.95/0.99      ( ~ v2_lattice3(X0) | ~ v2_struct_0(X0) | ~ l1_orders_2(X0) ),
% 1.95/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_647,plain,
% 1.95/0.99      ( ~ v2_struct_0(X0) | ~ l1_orders_2(X0) | sK3 != X0 ),
% 1.95/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_31]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_648,plain,
% 1.95/0.99      ( ~ v2_struct_0(sK3) | ~ l1_orders_2(sK3) ),
% 1.95/0.99      inference(unflattening,[status(thm)],[c_647]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_106,plain,
% 1.95/0.99      ( ~ v2_lattice3(sK3) | ~ v2_struct_0(sK3) | ~ l1_orders_2(sK3) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_650,plain,
% 1.95/0.99      ( ~ v2_struct_0(sK3) ),
% 1.95/0.99      inference(global_propositional_subsumption,
% 1.95/0.99                [status(thm)],
% 1.95/0.99                [c_648,c_31,c_29,c_70,c_106]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_775,plain,
% 1.95/0.99      ( ~ l1_orders_2(X0)
% 1.95/0.99      | ~ v1_relat_1(X1)
% 1.95/0.99      | k2_yellow_0(X0,k2_relat_1(X1)) = k5_yellow_2(X0,X1)
% 1.95/0.99      | sK3 != X0 ),
% 1.95/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_650]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_776,plain,
% 1.95/0.99      ( ~ l1_orders_2(sK3)
% 1.95/0.99      | ~ v1_relat_1(X0)
% 1.95/0.99      | k2_yellow_0(sK3,k2_relat_1(X0)) = k5_yellow_2(sK3,X0) ),
% 1.95/0.99      inference(unflattening,[status(thm)],[c_775]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_780,plain,
% 1.95/0.99      ( ~ v1_relat_1(X0)
% 1.95/0.99      | k2_yellow_0(sK3,k2_relat_1(X0)) = k5_yellow_2(sK3,X0) ),
% 1.95/0.99      inference(global_propositional_subsumption,
% 1.95/0.99                [status(thm)],
% 1.95/0.99                [c_776,c_29,c_70]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2088,plain,
% 1.95/0.99      ( ~ v1_relat_1(X0_66)
% 1.95/0.99      | k2_yellow_0(sK3,k2_relat_1(X0_66)) = k5_yellow_2(sK3,X0_66) ),
% 1.95/0.99      inference(subtyping,[status(esa)],[c_780]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2526,plain,
% 1.95/0.99      ( k2_yellow_0(sK3,k2_relat_1(X0_66)) = k5_yellow_2(sK3,X0_66)
% 1.95/0.99      | v1_relat_1(X0_66) != iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_2088]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3108,plain,
% 1.95/0.99      ( k2_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = k5_yellow_2(sK3,u1_waybel_0(sK3,sK5)) ),
% 1.95/0.99      inference(superposition,[status(thm)],[c_2780,c_2526]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_13,plain,
% 1.95/0.99      ( ~ l1_waybel_0(X0,X1)
% 1.95/0.99      | v2_struct_0(X1)
% 1.95/0.99      | ~ l1_orders_2(X1)
% 1.95/0.99      | k5_yellow_2(X1,u1_waybel_0(X1,X0)) = k1_waybel_9(X1,X0) ),
% 1.95/0.99      inference(cnf_transformation,[],[f63]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_749,plain,
% 1.95/0.99      ( v2_struct_0(X0)
% 1.95/0.99      | ~ l1_orders_2(X0)
% 1.95/0.99      | k5_yellow_2(X0,u1_waybel_0(X0,X1)) = k1_waybel_9(X0,X1)
% 1.95/0.99      | sK5 != X1
% 1.95/0.99      | sK3 != X0 ),
% 1.95/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_24]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_750,plain,
% 1.95/0.99      ( v2_struct_0(sK3)
% 1.95/0.99      | ~ l1_orders_2(sK3)
% 1.95/0.99      | k5_yellow_2(sK3,u1_waybel_0(sK3,sK5)) = k1_waybel_9(sK3,sK5) ),
% 1.95/0.99      inference(unflattening,[status(thm)],[c_749]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_752,plain,
% 1.95/0.99      ( k5_yellow_2(sK3,u1_waybel_0(sK3,sK5)) = k1_waybel_9(sK3,sK5) ),
% 1.95/0.99      inference(global_propositional_subsumption,
% 1.95/0.99                [status(thm)],
% 1.95/0.99                [c_750,c_31,c_29,c_70,c_106]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2089,plain,
% 1.95/0.99      ( k5_yellow_2(sK3,u1_waybel_0(sK3,sK5)) = k1_waybel_9(sK3,sK5) ),
% 1.95/0.99      inference(subtyping,[status(esa)],[c_752]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3109,plain,
% 1.95/0.99      ( k2_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = k1_waybel_9(sK3,sK5) ),
% 1.95/0.99      inference(light_normalisation,[status(thm)],[c_3108,c_2089]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3252,plain,
% 1.95/0.99      ( k1_waybel_9(sK3,sK5) = X0_66
% 1.95/0.99      | r1_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_66) != iProver_top
% 1.95/0.99      | r1_orders_2(sK3,sK0(sK3,X0_66,k2_relat_1(u1_waybel_0(sK3,sK5))),sK4) = iProver_top
% 1.95/0.99      | m1_subset_1(X0_66,u1_struct_0(sK3)) != iProver_top
% 1.95/0.99      | m1_subset_1(sK0(sK3,X0_66,k2_relat_1(u1_waybel_0(sK3,sK5))),u1_struct_0(sK3)) != iProver_top ),
% 1.95/0.99      inference(demodulation,[status(thm)],[c_3059,c_3109]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3262,plain,
% 1.95/0.99      ( k1_waybel_9(sK3,sK5) = X0_66
% 1.95/0.99      | k2_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = X0_66
% 1.95/0.99      | r1_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_66) != iProver_top
% 1.95/0.99      | r1_orders_2(sK3,sK0(sK3,X0_66,k2_relat_1(u1_waybel_0(sK3,sK5))),sK4) = iProver_top
% 1.95/0.99      | m1_subset_1(X0_66,u1_struct_0(sK3)) != iProver_top ),
% 1.95/0.99      inference(superposition,[status(thm)],[c_2535,c_3252]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3268,plain,
% 1.95/0.99      ( k1_waybel_9(sK3,sK5) = X0_66
% 1.95/0.99      | r1_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_66) != iProver_top
% 1.95/0.99      | r1_orders_2(sK3,sK0(sK3,X0_66,k2_relat_1(u1_waybel_0(sK3,sK5))),sK4) = iProver_top
% 1.95/0.99      | m1_subset_1(X0_66,u1_struct_0(sK3)) != iProver_top ),
% 1.95/0.99      inference(demodulation,[status(thm)],[c_3262,c_3109]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_7,plain,
% 1.95/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 1.95/0.99      | ~ r1_orders_2(X0,sK0(X0,X2,X1),X2)
% 1.95/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.95/0.99      | ~ v5_orders_2(X0)
% 1.95/0.99      | ~ l1_orders_2(X0)
% 1.95/0.99      | k2_yellow_0(X0,X1) = X2 ),
% 1.95/0.99      inference(cnf_transformation,[],[f58]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_1030,plain,
% 1.95/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 1.95/0.99      | ~ r1_orders_2(X0,sK0(X0,X2,X1),X2)
% 1.95/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.95/0.99      | ~ l1_orders_2(X0)
% 1.95/0.99      | k2_yellow_0(X0,X1) = X2
% 1.95/0.99      | sK3 != X0 ),
% 1.95/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_33]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_1031,plain,
% 1.95/0.99      ( ~ r1_lattice3(sK3,X0,X1)
% 1.95/0.99      | ~ r1_orders_2(sK3,sK0(sK3,X1,X0),X1)
% 1.95/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.95/0.99      | ~ l1_orders_2(sK3)
% 1.95/0.99      | k2_yellow_0(sK3,X0) = X1 ),
% 1.95/0.99      inference(unflattening,[status(thm)],[c_1030]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_1035,plain,
% 1.95/0.99      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.95/0.99      | ~ r1_orders_2(sK3,sK0(sK3,X1,X0),X1)
% 1.95/0.99      | ~ r1_lattice3(sK3,X0,X1)
% 1.95/0.99      | k2_yellow_0(sK3,X0) = X1 ),
% 1.95/0.99      inference(global_propositional_subsumption,
% 1.95/0.99                [status(thm)],
% 1.95/0.99                [c_1031,c_29,c_70]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_1036,plain,
% 1.95/0.99      ( ~ r1_lattice3(sK3,X0,X1)
% 1.95/0.99      | ~ r1_orders_2(sK3,sK0(sK3,X1,X0),X1)
% 1.95/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.95/0.99      | k2_yellow_0(sK3,X0) = X1 ),
% 1.95/0.99      inference(renaming,[status(thm)],[c_1035]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2079,plain,
% 1.95/0.99      ( ~ r1_lattice3(sK3,X0_68,X0_66)
% 1.95/0.99      | ~ r1_orders_2(sK3,sK0(sK3,X0_66,X0_68),X0_66)
% 1.95/0.99      | ~ m1_subset_1(X0_66,u1_struct_0(sK3))
% 1.95/0.99      | k2_yellow_0(sK3,X0_68) = X0_66 ),
% 1.95/0.99      inference(subtyping,[status(esa)],[c_1036]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2537,plain,
% 1.95/0.99      ( k2_yellow_0(sK3,X0_68) = X0_66
% 1.95/0.99      | r1_lattice3(sK3,X0_68,X0_66) != iProver_top
% 1.95/0.99      | r1_orders_2(sK3,sK0(sK3,X0_66,X0_68),X0_66) != iProver_top
% 1.95/0.99      | m1_subset_1(X0_66,u1_struct_0(sK3)) != iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_2079]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3470,plain,
% 1.95/0.99      ( k1_waybel_9(sK3,sK5) = sK4
% 1.95/0.99      | k2_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = sK4
% 1.95/0.99      | r1_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),sK4) != iProver_top
% 1.95/0.99      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 1.95/0.99      inference(superposition,[status(thm)],[c_3268,c_2537]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_3475,plain,
% 1.95/0.99      ( k1_waybel_9(sK3,sK5) = sK4
% 1.95/0.99      | r1_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),sK4) != iProver_top
% 1.95/0.99      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 1.95/0.99      inference(demodulation,[status(thm)],[c_3470,c_3109]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_16,plain,
% 1.95/0.99      ( ~ v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0)
% 1.95/0.99      | ~ r3_waybel_9(X0,X1,X2)
% 1.95/0.99      | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
% 1.95/0.99      | ~ v11_waybel_0(X1,X0)
% 1.95/0.99      | ~ l1_waybel_0(X1,X0)
% 1.95/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.95/0.99      | ~ v2_pre_topc(X0)
% 1.95/0.99      | ~ v8_pre_topc(X0)
% 1.95/0.99      | ~ v3_orders_2(X0)
% 1.95/0.99      | ~ v1_lattice3(X0)
% 1.95/0.99      | ~ v1_compts_1(X0)
% 1.95/0.99      | ~ v4_orders_2(X1)
% 1.95/0.99      | ~ v4_orders_2(X0)
% 1.95/0.99      | ~ v7_waybel_0(X1)
% 1.95/0.99      | ~ l1_waybel_9(X0)
% 1.95/0.99      | ~ v5_orders_2(X0)
% 1.95/0.99      | ~ v2_lattice3(X0)
% 1.95/0.99      | v2_struct_0(X1) ),
% 1.95/0.99      inference(cnf_transformation,[],[f90]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_22,negated_conjecture,
% 1.95/0.99      ( v11_waybel_0(sK5,sK3) ),
% 1.95/0.99      inference(cnf_transformation,[],[f85]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_475,plain,
% 1.95/0.99      ( ~ v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0)
% 1.95/0.99      | ~ r3_waybel_9(X0,X1,X2)
% 1.95/0.99      | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
% 1.95/0.99      | ~ l1_waybel_0(X1,X0)
% 1.95/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.95/0.99      | ~ v2_pre_topc(X0)
% 1.95/0.99      | ~ v8_pre_topc(X0)
% 1.95/0.99      | ~ v3_orders_2(X0)
% 1.95/0.99      | ~ v1_lattice3(X0)
% 1.95/0.99      | ~ v1_compts_1(X0)
% 1.95/0.99      | ~ v4_orders_2(X1)
% 1.95/0.99      | ~ v4_orders_2(X0)
% 1.95/0.99      | ~ v7_waybel_0(X1)
% 1.95/0.99      | ~ l1_waybel_9(X0)
% 1.95/0.99      | ~ v5_orders_2(X0)
% 1.95/0.99      | ~ v2_lattice3(X0)
% 1.95/0.99      | v2_struct_0(X1)
% 1.95/0.99      | sK5 != X1
% 1.95/0.99      | sK3 != X0 ),
% 1.95/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_476,plain,
% 1.95/0.99      ( ~ v5_pre_topc(k4_waybel_1(sK3,sK1(sK3)),sK3,sK3)
% 1.95/0.99      | ~ r3_waybel_9(sK3,sK5,X0)
% 1.95/0.99      | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.95/0.99      | ~ l1_waybel_0(sK5,sK3)
% 1.95/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.95/0.99      | ~ v2_pre_topc(sK3)
% 1.95/0.99      | ~ v8_pre_topc(sK3)
% 1.95/0.99      | ~ v3_orders_2(sK3)
% 1.95/0.99      | ~ v1_lattice3(sK3)
% 1.95/0.99      | ~ v1_compts_1(sK3)
% 1.95/0.99      | ~ v4_orders_2(sK5)
% 1.95/0.99      | ~ v4_orders_2(sK3)
% 1.95/0.99      | ~ v7_waybel_0(sK5)
% 1.95/0.99      | ~ l1_waybel_9(sK3)
% 1.95/0.99      | ~ v5_orders_2(sK3)
% 1.95/0.99      | ~ v2_lattice3(sK3)
% 1.95/0.99      | v2_struct_0(sK5) ),
% 1.95/0.99      inference(unflattening,[status(thm)],[c_475]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_480,plain,
% 1.95/0.99      ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.95/0.99      | ~ r3_waybel_9(sK3,sK5,X0)
% 1.95/0.99      | ~ v5_pre_topc(k4_waybel_1(sK3,sK1(sK3)),sK3,sK3)
% 1.95/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 1.95/0.99      inference(global_propositional_subsumption,
% 1.95/0.99                [status(thm)],
% 1.95/0.99                [c_476,c_37,c_36,c_35,c_34,c_33,c_32,c_31,c_30,c_29,c_27,
% 1.95/0.99                 c_26,c_25,c_24]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_481,plain,
% 1.95/0.99      ( ~ v5_pre_topc(k4_waybel_1(sK3,sK1(sK3)),sK3,sK3)
% 1.95/0.99      | ~ r3_waybel_9(sK3,sK5,X0)
% 1.95/0.99      | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.95/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 1.95/0.99      inference(renaming,[status(thm)],[c_480]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_554,plain,
% 1.95/0.99      ( ~ r3_waybel_9(sK3,sK5,X0)
% 1.95/0.99      | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.95/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.95/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.95/0.99      | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X1)
% 1.95/0.99      | sK3 != sK3 ),
% 1.95/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_481]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_881,plain,
% 1.95/0.99      ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.95/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.95/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.95/0.99      | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X1)
% 1.95/0.99      | sK4 != X0
% 1.95/0.99      | sK5 != sK5
% 1.95/0.99      | sK3 != sK3 ),
% 1.95/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_554]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_882,plain,
% 1.95/0.99      ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
% 1.95/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.95/0.99      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 1.95/0.99      | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0) ),
% 1.95/0.99      inference(unflattening,[status(thm)],[c_881]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_886,plain,
% 1.95/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.95/0.99      | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
% 1.95/0.99      | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0) ),
% 1.95/0.99      inference(global_propositional_subsumption,
% 1.95/0.99                [status(thm)],
% 1.95/0.99                [c_882,c_28]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_887,plain,
% 1.95/0.99      ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
% 1.95/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.95/0.99      | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0) ),
% 1.95/0.99      inference(renaming,[status(thm)],[c_886]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2085,plain,
% 1.95/0.99      ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
% 1.95/0.99      | ~ m1_subset_1(X0_66,u1_struct_0(sK3))
% 1.95/0.99      | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0_66) ),
% 1.95/0.99      inference(subtyping,[status(esa)],[c_887]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2531,plain,
% 1.95/0.99      ( k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0_66)
% 1.95/0.99      | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) = iProver_top
% 1.95/0.99      | m1_subset_1(X0_66,u1_struct_0(sK3)) != iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_2085]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_17,plain,
% 1.95/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 1.95/0.99      | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
% 1.95/0.99      | ~ v11_waybel_0(X1,X0)
% 1.95/0.99      | ~ l1_waybel_0(X1,X0)
% 1.95/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.95/0.99      | m1_subset_1(sK1(X0),u1_struct_0(X0))
% 1.95/0.99      | ~ v2_pre_topc(X0)
% 1.95/0.99      | ~ v8_pre_topc(X0)
% 1.95/0.99      | ~ v3_orders_2(X0)
% 1.95/0.99      | ~ v1_lattice3(X0)
% 1.95/0.99      | ~ v1_compts_1(X0)
% 1.95/0.99      | ~ v4_orders_2(X1)
% 1.95/0.99      | ~ v4_orders_2(X0)
% 1.95/0.99      | ~ v7_waybel_0(X1)
% 1.95/0.99      | ~ l1_waybel_9(X0)
% 1.95/0.99      | ~ v5_orders_2(X0)
% 1.95/0.99      | ~ v2_lattice3(X0)
% 1.95/0.99      | v2_struct_0(X1) ),
% 1.95/0.99      inference(cnf_transformation,[],[f91]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_451,plain,
% 1.95/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 1.95/0.99      | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
% 1.95/0.99      | ~ l1_waybel_0(X1,X0)
% 1.95/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.95/0.99      | m1_subset_1(sK1(X0),u1_struct_0(X0))
% 1.95/0.99      | ~ v2_pre_topc(X0)
% 1.95/0.99      | ~ v8_pre_topc(X0)
% 1.95/0.99      | ~ v3_orders_2(X0)
% 1.95/0.99      | ~ v1_lattice3(X0)
% 1.95/0.99      | ~ v1_compts_1(X0)
% 1.95/0.99      | ~ v4_orders_2(X1)
% 1.95/0.99      | ~ v4_orders_2(X0)
% 1.95/0.99      | ~ v7_waybel_0(X1)
% 1.95/0.99      | ~ l1_waybel_9(X0)
% 1.95/0.99      | ~ v5_orders_2(X0)
% 1.95/0.99      | ~ v2_lattice3(X0)
% 1.95/0.99      | v2_struct_0(X1)
% 1.95/0.99      | sK5 != X1
% 1.95/0.99      | sK3 != X0 ),
% 1.95/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_22]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_452,plain,
% 1.95/0.99      ( ~ r3_waybel_9(sK3,sK5,X0)
% 1.95/0.99      | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.95/0.99      | ~ l1_waybel_0(sK5,sK3)
% 1.95/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.95/0.99      | m1_subset_1(sK1(sK3),u1_struct_0(sK3))
% 1.95/0.99      | ~ v2_pre_topc(sK3)
% 1.95/0.99      | ~ v8_pre_topc(sK3)
% 1.95/0.99      | ~ v3_orders_2(sK3)
% 1.95/0.99      | ~ v1_lattice3(sK3)
% 1.95/0.99      | ~ v1_compts_1(sK3)
% 1.95/0.99      | ~ v4_orders_2(sK5)
% 1.95/0.99      | ~ v4_orders_2(sK3)
% 1.95/0.99      | ~ v7_waybel_0(sK5)
% 1.95/0.99      | ~ l1_waybel_9(sK3)
% 1.95/0.99      | ~ v5_orders_2(sK3)
% 1.95/0.99      | ~ v2_lattice3(sK3)
% 1.95/0.99      | v2_struct_0(sK5) ),
% 1.95/0.99      inference(unflattening,[status(thm)],[c_451]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_456,plain,
% 1.95/0.99      ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.95/0.99      | ~ r3_waybel_9(sK3,sK5,X0)
% 1.95/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.95/0.99      | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) ),
% 1.95/0.99      inference(global_propositional_subsumption,
% 1.95/0.99                [status(thm)],
% 1.95/0.99                [c_452,c_37,c_36,c_35,c_34,c_33,c_32,c_31,c_30,c_29,c_27,
% 1.95/0.99                 c_26,c_25,c_24]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_457,plain,
% 1.95/0.99      ( ~ r3_waybel_9(sK3,sK5,X0)
% 1.95/0.99      | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.95/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.95/0.99      | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) ),
% 1.95/0.99      inference(renaming,[status(thm)],[c_456]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_902,plain,
% 1.95/0.99      ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.95/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.95/0.99      | m1_subset_1(sK1(sK3),u1_struct_0(sK3))
% 1.95/0.99      | sK4 != X0
% 1.95/0.99      | sK5 != sK5
% 1.95/0.99      | sK3 != sK3 ),
% 1.95/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_457]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_903,plain,
% 1.95/0.99      ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
% 1.95/0.99      | m1_subset_1(sK1(sK3),u1_struct_0(sK3))
% 1.95/0.99      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 1.95/0.99      inference(unflattening,[status(thm)],[c_902]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_905,plain,
% 1.95/0.99      ( m1_subset_1(sK1(sK3),u1_struct_0(sK3))
% 1.95/0.99      | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) ),
% 1.95/0.99      inference(global_propositional_subsumption,
% 1.95/0.99                [status(thm)],
% 1.95/0.99                [c_903,c_28]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_906,plain,
% 1.95/0.99      ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
% 1.95/0.99      | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) ),
% 1.95/0.99      inference(renaming,[status(thm)],[c_905]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_907,plain,
% 1.95/0.99      ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) = iProver_top
% 1.95/0.99      | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_906]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2103,plain,( X0_70 = X0_70 ),theory(equality) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2718,plain,
% 1.95/0.99      ( k4_waybel_1(sK3,sK1(sK3)) = k4_waybel_1(sK3,sK1(sK3)) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_2103]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2719,plain,
% 1.95/0.99      ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
% 1.95/0.99      | ~ m1_subset_1(sK1(sK3),u1_struct_0(sK3))
% 1.95/0.99      | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,sK1(sK3)) ),
% 1.95/0.99      inference(instantiation,[status(thm)],[c_2085]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2720,plain,
% 1.95/0.99      ( k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,sK1(sK3))
% 1.95/0.99      | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) = iProver_top
% 1.95/0.99      | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) != iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_2719]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2758,plain,
% 1.95/0.99      ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) = iProver_top ),
% 1.95/0.99      inference(global_propositional_subsumption,
% 1.95/0.99                [status(thm)],
% 1.95/0.99                [c_2531,c_907,c_2718,c_2720]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2837,plain,
% 1.95/0.99      ( r1_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),sK4) = iProver_top ),
% 1.95/0.99      inference(demodulation,[status(thm)],[c_2785,c_2758]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_20,negated_conjecture,
% 1.95/0.99      ( k1_waybel_9(sK3,sK5) != sK4 ),
% 1.95/0.99      inference(cnf_transformation,[],[f87]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_2092,negated_conjecture,
% 1.95/0.99      ( k1_waybel_9(sK3,sK5) != sK4 ),
% 1.95/0.99      inference(subtyping,[status(esa)],[c_20]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(c_47,plain,
% 1.95/0.99      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 1.95/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 1.95/0.99  
% 1.95/0.99  cnf(contradiction,plain,
% 1.95/0.99      ( $false ),
% 1.95/0.99      inference(minisat,[status(thm)],[c_3475,c_2837,c_2092,c_47]) ).
% 1.95/0.99  
% 1.95/0.99  
% 1.95/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.95/0.99  
% 1.95/0.99  ------                               Statistics
% 1.95/0.99  
% 1.95/0.99  ------ General
% 1.95/0.99  
% 1.95/0.99  abstr_ref_over_cycles:                  0
% 1.95/0.99  abstr_ref_under_cycles:                 0
% 1.95/0.99  gc_basic_clause_elim:                   0
% 1.95/0.99  forced_gc_time:                         0
% 1.95/0.99  parsing_time:                           0.011
% 1.95/0.99  unif_index_cands_time:                  0.
% 1.95/0.99  unif_index_add_time:                    0.
% 1.95/0.99  orderings_time:                         0.
% 1.95/0.99  out_proof_time:                         0.015
% 1.95/0.99  total_time:                             0.171
% 1.95/0.99  num_of_symbols:                         74
% 1.95/0.99  num_of_terms:                           2326
% 1.95/0.99  
% 1.95/0.99  ------ Preprocessing
% 1.95/0.99  
% 1.95/0.99  num_of_splits:                          2
% 1.95/0.99  num_of_split_atoms:                     2
% 1.95/0.99  num_of_reused_defs:                     0
% 1.95/0.99  num_eq_ax_congr_red:                    27
% 1.95/0.99  num_of_sem_filtered_clauses:            1
% 1.95/0.99  num_of_subtypes:                        6
% 1.95/0.99  monotx_restored_types:                  0
% 1.95/0.99  sat_num_of_epr_types:                   0
% 1.95/0.99  sat_num_of_non_cyclic_types:            0
% 1.95/0.99  sat_guarded_non_collapsed_types:        1
% 1.95/0.99  num_pure_diseq_elim:                    0
% 1.95/0.99  simp_replaced_by:                       0
% 1.95/0.99  res_preprocessed:                       155
% 1.95/0.99  prep_upred:                             0
% 1.95/0.99  prep_unflattend:                        54
% 1.95/0.99  smt_new_axioms:                         0
% 1.95/0.99  pred_elim_cands:                        5
% 1.95/0.99  pred_elim:                              17
% 1.95/0.99  pred_elim_cl:                           18
% 1.95/0.99  pred_elim_cycles:                       25
% 1.95/0.99  merged_defs:                            0
% 1.95/0.99  merged_defs_ncl:                        0
% 1.95/0.99  bin_hyper_res:                          0
% 1.95/0.99  prep_cycles:                            4
% 1.95/0.99  pred_elim_time:                         0.036
% 1.95/0.99  splitting_time:                         0.
% 1.95/0.99  sem_filter_time:                        0.
% 1.95/0.99  monotx_time:                            0.
% 1.95/0.99  subtype_inf_time:                       0.
% 1.95/0.99  
% 1.95/0.99  ------ Problem properties
% 1.95/0.99  
% 1.95/0.99  clauses:                                22
% 1.95/0.99  conjectures:                            2
% 1.95/0.99  epr:                                    1
% 1.95/0.99  horn:                                   15
% 1.95/0.99  ground:                                 6
% 1.95/0.99  unary:                                  4
% 1.95/0.99  binary:                                 5
% 1.95/0.99  lits:                                   63
% 1.95/0.99  lits_eq:                                11
% 1.95/0.99  fd_pure:                                0
% 1.95/0.99  fd_pseudo:                              0
% 1.95/0.99  fd_cond:                                0
% 1.95/0.99  fd_pseudo_cond:                         3
% 1.95/0.99  ac_symbols:                             0
% 1.95/0.99  
% 1.95/0.99  ------ Propositional Solver
% 1.95/0.99  
% 1.95/0.99  prop_solver_calls:                      25
% 1.95/0.99  prop_fast_solver_calls:                 1557
% 1.95/0.99  smt_solver_calls:                       0
% 1.95/0.99  smt_fast_solver_calls:                  0
% 1.95/0.99  prop_num_of_clauses:                    811
% 1.95/0.99  prop_preprocess_simplified:             4413
% 1.95/0.99  prop_fo_subsumed:                       81
% 1.95/0.99  prop_solver_time:                       0.
% 1.95/0.99  smt_solver_time:                        0.
% 1.95/0.99  smt_fast_solver_time:                   0.
% 1.95/0.99  prop_fast_solver_time:                  0.
% 1.95/0.99  prop_unsat_core_time:                   0.
% 1.95/0.99  
% 1.95/0.99  ------ QBF
% 1.95/0.99  
% 1.95/0.99  qbf_q_res:                              0
% 1.95/0.99  qbf_num_tautologies:                    0
% 1.95/0.99  qbf_prep_cycles:                        0
% 1.95/0.99  
% 1.95/0.99  ------ BMC1
% 1.95/0.99  
% 1.95/0.99  bmc1_current_bound:                     -1
% 1.95/0.99  bmc1_last_solved_bound:                 -1
% 1.95/0.99  bmc1_unsat_core_size:                   -1
% 1.95/0.99  bmc1_unsat_core_parents_size:           -1
% 1.95/0.99  bmc1_merge_next_fun:                    0
% 1.95/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.95/0.99  
% 1.95/0.99  ------ Instantiation
% 1.95/0.99  
% 1.95/0.99  inst_num_of_clauses:                    197
% 1.95/0.99  inst_num_in_passive:                    4
% 1.95/0.99  inst_num_in_active:                     137
% 1.95/0.99  inst_num_in_unprocessed:                56
% 1.95/0.99  inst_num_of_loops:                      150
% 1.95/0.99  inst_num_of_learning_restarts:          0
% 1.95/0.99  inst_num_moves_active_passive:          10
% 1.95/0.99  inst_lit_activity:                      0
% 1.95/0.99  inst_lit_activity_moves:                0
% 1.95/0.99  inst_num_tautologies:                   0
% 1.95/0.99  inst_num_prop_implied:                  0
% 1.95/0.99  inst_num_existing_simplified:           0
% 1.95/0.99  inst_num_eq_res_simplified:             0
% 1.95/0.99  inst_num_child_elim:                    0
% 1.95/0.99  inst_num_of_dismatching_blockings:      15
% 1.95/0.99  inst_num_of_non_proper_insts:           141
% 1.95/0.99  inst_num_of_duplicates:                 0
% 1.95/0.99  inst_inst_num_from_inst_to_res:         0
% 1.95/0.99  inst_dismatching_checking_time:         0.
% 1.95/0.99  
% 1.95/0.99  ------ Resolution
% 1.95/0.99  
% 1.95/0.99  res_num_of_clauses:                     0
% 1.95/0.99  res_num_in_passive:                     0
% 1.95/0.99  res_num_in_active:                      0
% 1.95/0.99  res_num_of_loops:                       159
% 1.95/0.99  res_forward_subset_subsumed:            34
% 1.95/0.99  res_backward_subset_subsumed:           0
% 1.95/0.99  res_forward_subsumed:                   0
% 1.95/0.99  res_backward_subsumed:                  0
% 1.95/0.99  res_forward_subsumption_resolution:     2
% 1.95/0.99  res_backward_subsumption_resolution:    0
% 1.95/0.99  res_clause_to_clause_subsumption:       116
% 1.95/0.99  res_orphan_elimination:                 0
% 1.95/0.99  res_tautology_del:                      16
% 1.95/0.99  res_num_eq_res_simplified:              0
% 1.95/0.99  res_num_sel_changes:                    0
% 1.95/0.99  res_moves_from_active_to_pass:          0
% 1.95/0.99  
% 1.95/0.99  ------ Superposition
% 1.95/0.99  
% 1.95/0.99  sup_time_total:                         0.
% 1.95/0.99  sup_time_generating:                    0.
% 1.95/0.99  sup_time_sim_full:                      0.
% 1.95/0.99  sup_time_sim_immed:                     0.
% 1.95/0.99  
% 1.95/0.99  sup_num_of_clauses:                     34
% 1.95/0.99  sup_num_in_active:                      28
% 1.95/0.99  sup_num_in_passive:                     6
% 1.95/0.99  sup_num_of_loops:                       29
% 1.95/0.99  sup_fw_superposition:                   10
% 1.95/0.99  sup_bw_superposition:                   7
% 1.95/0.99  sup_immediate_simplified:               9
% 1.95/0.99  sup_given_eliminated:                   0
% 1.95/0.99  comparisons_done:                       0
% 1.95/0.99  comparisons_avoided:                    0
% 1.95/0.99  
% 1.95/0.99  ------ Simplifications
% 1.95/0.99  
% 1.95/0.99  
% 1.95/0.99  sim_fw_subset_subsumed:                 0
% 1.95/0.99  sim_bw_subset_subsumed:                 3
% 1.95/0.99  sim_fw_subsumed:                        2
% 1.95/0.99  sim_bw_subsumed:                        0
% 1.95/0.99  sim_fw_subsumption_res:                 0
% 1.95/0.99  sim_bw_subsumption_res:                 0
% 1.95/0.99  sim_tautology_del:                      1
% 1.95/0.99  sim_eq_tautology_del:                   0
% 1.95/0.99  sim_eq_res_simp:                        0
% 1.95/0.99  sim_fw_demodulated:                     4
% 1.95/0.99  sim_bw_demodulated:                     1
% 1.95/0.99  sim_light_normalised:                   4
% 1.95/0.99  sim_joinable_taut:                      0
% 1.95/0.99  sim_joinable_simp:                      0
% 1.95/0.99  sim_ac_normalised:                      0
% 1.95/0.99  sim_smt_subsumption:                    0
% 1.95/0.99  
%------------------------------------------------------------------------------
