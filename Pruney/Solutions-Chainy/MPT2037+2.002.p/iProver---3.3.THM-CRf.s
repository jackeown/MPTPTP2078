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
% DateTime   : Thu Dec  3 12:28:59 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :  242 (2257 expanded)
%              Number of clauses        :  156 ( 487 expanded)
%              Number of leaves         :   19 ( 742 expanded)
%              Depth                    :   34
%              Number of atoms          : 1497 (32643 expanded)
%              Number of equality atoms :  225 (2270 expanded)
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

fof(f23,plain,(
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
    inference(flattening,[],[f23])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X1)
          & r1_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X1)
        & r1_lattice3(X0,X2,sK0(X0,X1,X2))
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f38])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X2) = X1
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f36,plain,(
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
    inference(flattening,[],[f36])).

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f45,plain,
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

fof(f48,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f37,f47,f46,f45])).

fof(f74,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f78,plain,(
    l1_waybel_9(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => ( l1_orders_2(X0)
        & l1_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & l1_pre_topc(X0) )
      | ~ l1_waybel_9(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f65,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X2) = X1
      | r1_lattice3(X0,X2,sK0(X0,X1,X2))
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f86,plain,(
    r3_waybel_9(sK3,sK5,sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f82,plain,(
    v7_waybel_0(sK5) ),
    inference(cnf_transformation,[],[f48])).

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

fof(f34,plain,(
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
    inference(flattening,[],[f34])).

fof(f42,plain,(
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
    inference(rectify,[],[f35])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X5] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X5),X0,X0)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0)
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).

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
    inference(cnf_transformation,[],[f44])).

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
    inference(cnf_transformation,[],[f48])).

fof(f70,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f71,plain,(
    v8_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f72,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f73,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f75,plain,(
    v1_lattice3(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f76,plain,(
    v2_lattice3(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f77,plain,(
    v1_compts_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f80,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f81,plain,(
    v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f83,plain,(
    l1_waybel_0(sK5,sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f79,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f48])).

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
    inference(cnf_transformation,[],[f44])).

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

fof(f16,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f64,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_yellow_0(X0,k2_relat_1(X1)) = k5_yellow_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow_0(X0,k2_relat_1(X1)) = k5_yellow_2(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow_0(X0,k2_relat_1(X1)) = k5_yellow_2(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_yellow_0(X0,k2_relat_1(X1)) = k5_yellow_2(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1))
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1))
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X2) = X1
      | ~ r1_orders_2(X0,sK0(X0,X1,X2),X1)
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f32,plain,(
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
    inference(flattening,[],[f32])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X4] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0)
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f40])).

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
    inference(cnf_transformation,[],[f41])).

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
    inference(cnf_transformation,[],[f48])).

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
    inference(cnf_transformation,[],[f41])).

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
    inference(cnf_transformation,[],[f48])).

cnf(c_9,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_34,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1019,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X2,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_34])).

cnf(c_1020,plain,
    ( ~ r1_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK0(sK3,X1,X0),u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | k2_yellow_0(sK3,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1019])).

cnf(c_30,negated_conjecture,
    ( l1_waybel_9(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_15,plain,
    ( ~ l1_waybel_9(X0)
    | l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_74,plain,
    ( ~ l1_waybel_9(sK3)
    | l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1024,plain,
    ( m1_subset_1(sK0(sK3,X1,X0),u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r1_lattice3(sK3,X0,X1)
    | k2_yellow_0(sK3,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1020,c_30,c_74])).

cnf(c_1025,plain,
    ( ~ r1_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK0(sK3,X1,X0),u1_struct_0(sK3))
    | k2_yellow_0(sK3,X0) = X1 ),
    inference(renaming,[status(thm)],[c_1024])).

cnf(c_2118,plain,
    ( ~ r1_lattice3(sK3,X0_69,X0_67)
    | ~ m1_subset_1(X0_67,u1_struct_0(sK3))
    | m1_subset_1(sK0(sK3,X0_67,X0_69),u1_struct_0(sK3))
    | k2_yellow_0(sK3,X0_69) = X0_67 ),
    inference(subtyping,[status(esa)],[c_1025])).

cnf(c_2572,plain,
    ( k2_yellow_0(sK3,X0_69) = X0_67
    | r1_lattice3(sK3,X0_69,X0_67) != iProver_top
    | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK0(sK3,X0_67,X0_69),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2118])).

cnf(c_8,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X1,sK0(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1043,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X1,sK0(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_34])).

cnf(c_1044,plain,
    ( ~ r1_lattice3(sK3,X0,X1)
    | r1_lattice3(sK3,X0,sK0(sK3,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | k2_yellow_0(sK3,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1043])).

cnf(c_1048,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r1_lattice3(sK3,X0,sK0(sK3,X1,X0))
    | ~ r1_lattice3(sK3,X0,X1)
    | k2_yellow_0(sK3,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1044,c_30,c_74])).

cnf(c_1049,plain,
    ( ~ r1_lattice3(sK3,X0,X1)
    | r1_lattice3(sK3,X0,sK0(sK3,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k2_yellow_0(sK3,X0) = X1 ),
    inference(renaming,[status(thm)],[c_1048])).

cnf(c_2117,plain,
    ( ~ r1_lattice3(sK3,X0_69,X0_67)
    | r1_lattice3(sK3,X0_69,sK0(sK3,X0_67,X0_69))
    | ~ m1_subset_1(X0_67,u1_struct_0(sK3))
    | k2_yellow_0(sK3,X0_69) = X0_67 ),
    inference(subtyping,[status(esa)],[c_1049])).

cnf(c_2573,plain,
    ( k2_yellow_0(sK3,X0_69) = X0_67
    | r1_lattice3(sK3,X0_69,X0_67) != iProver_top
    | r1_lattice3(sK3,X0_69,sK0(sK3,X0_67,X0_69)) = iProver_top
    | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2117])).

cnf(c_22,negated_conjecture,
    ( r3_waybel_9(sK3,sK5,sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_26,negated_conjecture,
    ( v7_waybel_0(sK5) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_19,plain,
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
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_24,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(sK3,X0),sK3,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_535,plain,
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
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | k4_waybel_1(X0,sK2(X0)) != k4_waybel_1(sK3,X4)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_24])).

cnf(c_536,plain,
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
    | ~ v2_lattice3(sK3)
    | ~ v1_compts_1(sK3)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK3)
    | ~ v7_waybel_0(X0)
    | ~ l1_waybel_9(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v1_lattice3(sK3)
    | v2_struct_0(X0)
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X3) ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_38,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_37,negated_conjecture,
    ( v8_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_36,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_35,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_33,negated_conjecture,
    ( v1_lattice3(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_32,negated_conjecture,
    ( v2_lattice3(sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_31,negated_conjecture,
    ( v1_compts_1(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_540,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_536,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_31,c_30])).

cnf(c_541,plain,
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
    inference(renaming,[status(thm)],[c_540])).

cnf(c_731,plain,
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
    inference(resolution_lifted,[status(thm)],[c_26,c_541])).

cnf(c_732,plain,
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
    inference(unflattening,[status(thm)],[c_731])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_27,negated_conjecture,
    ( v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_25,negated_conjecture,
    ( l1_waybel_0(sK5,sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_736,plain,
    ( r1_orders_2(sK3,X1,X0)
    | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
    | ~ r3_waybel_9(sK3,sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_732,c_28,c_27,c_25])).

cnf(c_737,plain,
    ( ~ r3_waybel_9(sK3,sK5,X0)
    | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
    | r1_orders_2(sK3,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X2) ),
    inference(renaming,[status(thm)],[c_736])).

cnf(c_867,plain,
    ( ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | r1_orders_2(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X2)
    | sK4 != X1
    | sK5 != sK5
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_737])).

cnf(c_868,plain,
    ( ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | r1_orders_2(sK3,X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1) ),
    inference(unflattening,[status(thm)],[c_867])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_872,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r1_orders_2(sK3,X0,sK4)
    | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_868,c_29])).

cnf(c_873,plain,
    ( ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | r1_orders_2(sK3,X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1) ),
    inference(renaming,[status(thm)],[c_872])).

cnf(c_2124,plain,
    ( ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_67)
    | r1_orders_2(sK3,X0_67,sK4)
    | ~ m1_subset_1(X1_67,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_67,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1_67) ),
    inference(subtyping,[status(esa)],[c_873])).

cnf(c_2133,plain,
    ( ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_67)
    | r1_orders_2(sK3,X0_67,sK4)
    | ~ m1_subset_1(X0_67,u1_struct_0(sK3))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_2124])).

cnf(c_2565,plain,
    ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_67) != iProver_top
    | r1_orders_2(sK3,X0_67,sK4) = iProver_top
    | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2133])).

cnf(c_2134,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_2124])).

cnf(c_2196,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2134])).

cnf(c_2197,plain,
    ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_67) != iProver_top
    | r1_orders_2(sK3,X0_67,sK4) = iProver_top
    | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2133])).

cnf(c_20,plain,
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
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_611,plain,
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
    | ~ v2_lattice3(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_31])).

cnf(c_612,plain,
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
    | ~ v2_lattice3(sK3)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK3)
    | ~ v7_waybel_0(X0)
    | ~ l1_waybel_9(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v1_lattice3(sK3)
    | v2_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_611])).

cnf(c_616,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_612,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_30])).

cnf(c_617,plain,
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
    inference(renaming,[status(thm)],[c_616])).

cnf(c_701,plain,
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
    inference(resolution_lifted,[status(thm)],[c_26,c_617])).

cnf(c_702,plain,
    ( ~ r3_waybel_9(sK3,sK5,X0)
    | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
    | r1_orders_2(sK3,X1,X0)
    | ~ l1_waybel_0(sK5,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
    | ~ v4_orders_2(sK5)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_701])).

cnf(c_706,plain,
    ( r1_orders_2(sK3,X1,X0)
    | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
    | ~ r3_waybel_9(sK3,sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_702,c_28,c_27,c_25])).

cnf(c_707,plain,
    ( ~ r3_waybel_9(sK3,sK5,X0)
    | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
    | r1_orders_2(sK3,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_706])).

cnf(c_894,plain,
    ( ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | r1_orders_2(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
    | sK4 != X1
    | sK5 != sK5
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_707])).

cnf(c_895,plain,
    ( ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | r1_orders_2(sK3,X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_894])).

cnf(c_899,plain,
    ( m1_subset_1(sK2(sK3),u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r1_orders_2(sK3,X0,sK4)
    | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_895,c_29])).

cnf(c_900,plain,
    ( ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | r1_orders_2(sK3,X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_899])).

cnf(c_2123,plain,
    ( ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_67)
    | r1_orders_2(sK3,X0_67,sK4)
    | ~ m1_subset_1(X0_67,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_900])).

cnf(c_2203,plain,
    ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_67) != iProver_top
    | r1_orders_2(sK3,X0_67,sK4) = iProver_top
    | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2123])).

cnf(c_2132,plain,
    ( ~ m1_subset_1(X0_67,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X0_67)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_2124])).

cnf(c_2566,plain,
    ( k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X0_67)
    | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2132])).

cnf(c_2766,plain,
    ( m1_subset_1(sK2(sK3),u1_struct_0(sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2566])).

cnf(c_2980,plain,
    ( m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top
    | r1_orders_2(sK3,X0_67,sK4) = iProver_top
    | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_67) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2565,c_2196,c_2197,c_2203,c_2766])).

cnf(c_2981,plain,
    ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_67) != iProver_top
    | r1_orders_2(sK3,X0_67,sK4) = iProver_top
    | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2980])).

cnf(c_12,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_16,plain,
    ( ~ l1_waybel_9(X0)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_422,plain,
    ( ~ l1_waybel_9(X0)
    | l1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_16,c_2])).

cnf(c_436,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_waybel_9(X2)
    | X2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_422])).

cnf(c_437,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_waybel_9(X1) ),
    inference(unflattening,[status(thm)],[c_436])).

cnf(c_677,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_437,c_30])).

cnf(c_678,plain,
    ( ~ l1_waybel_0(X0,sK3)
    | m1_subset_1(u1_waybel_0(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) ),
    inference(unflattening,[status(thm)],[c_677])).

cnf(c_787,plain,
    ( m1_subset_1(u1_waybel_0(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
    | sK5 != X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_678])).

cnf(c_788,plain,
    ( m1_subset_1(u1_waybel_0(sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(unflattening,[status(thm)],[c_787])).

cnf(c_2126,plain,
    ( m1_subset_1(u1_waybel_0(sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_788])).

cnf(c_2562,plain,
    ( m1_subset_1(u1_waybel_0(sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2126])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2130,plain,
    ( ~ m1_subset_1(X0_67,k1_zfmisc_1(k2_zfmisc_1(X0_70,X1_70)))
    | k2_relset_1(X0_70,X1_70,X0_67) = k2_relat_1(X0_67) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2560,plain,
    ( k2_relset_1(X0_70,X1_70,X0_67) = k2_relat_1(X0_67)
    | m1_subset_1(X0_67,k1_zfmisc_1(k2_zfmisc_1(X0_70,X1_70))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2130])).

cnf(c_2822,plain,
    ( k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)) = k2_relat_1(u1_waybel_0(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_2562,c_2560])).

cnf(c_2986,plain,
    ( r1_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_67) != iProver_top
    | r1_orders_2(sK3,X0_67,sK4) = iProver_top
    | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2981,c_2822])).

cnf(c_3096,plain,
    ( k2_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = X0_67
    | r1_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_67) != iProver_top
    | r1_orders_2(sK3,sK0(sK3,X0_67,k2_relat_1(u1_waybel_0(sK3,sK5))),sK4) = iProver_top
    | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK0(sK3,X0_67,k2_relat_1(u1_waybel_0(sK3,sK5))),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2573,c_2986])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2131,plain,
    ( ~ m1_subset_1(X0_67,k1_zfmisc_1(k2_zfmisc_1(X0_70,X1_70)))
    | v1_relat_1(X0_67) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2559,plain,
    ( m1_subset_1(X0_67,k1_zfmisc_1(k2_zfmisc_1(X0_70,X1_70))) != iProver_top
    | v1_relat_1(X0_67) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2131])).

cnf(c_2817,plain,
    ( v1_relat_1(u1_waybel_0(sK3,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2562,c_2559])).

cnf(c_14,plain,
    ( ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v1_relat_1(X1)
    | k2_yellow_0(X0,k2_relat_1(X1)) = k5_yellow_2(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_3,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_664,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_33])).

cnf(c_665,plain,
    ( ~ l1_orders_2(sK3)
    | ~ v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_664])).

cnf(c_110,plain,
    ( ~ l1_orders_2(sK3)
    | ~ v1_lattice3(sK3)
    | ~ v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_667,plain,
    ( ~ v2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_665,c_33,c_30,c_74,c_110])).

cnf(c_812,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_relat_1(X1)
    | k2_yellow_0(X0,k2_relat_1(X1)) = k5_yellow_2(X0,X1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_667])).

cnf(c_813,plain,
    ( ~ l1_orders_2(sK3)
    | ~ v1_relat_1(X0)
    | k2_yellow_0(sK3,k2_relat_1(X0)) = k5_yellow_2(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_812])).

cnf(c_817,plain,
    ( ~ v1_relat_1(X0)
    | k2_yellow_0(sK3,k2_relat_1(X0)) = k5_yellow_2(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_813,c_30,c_74])).

cnf(c_2125,plain,
    ( ~ v1_relat_1(X0_67)
    | k2_yellow_0(sK3,k2_relat_1(X0_67)) = k5_yellow_2(sK3,X0_67) ),
    inference(subtyping,[status(esa)],[c_817])).

cnf(c_2563,plain,
    ( k2_yellow_0(sK3,k2_relat_1(X0_67)) = k5_yellow_2(sK3,X0_67)
    | v1_relat_1(X0_67) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2125])).

cnf(c_3145,plain,
    ( k2_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = k5_yellow_2(sK3,u1_waybel_0(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_2817,c_2563])).

cnf(c_13,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | k5_yellow_2(X1,u1_waybel_0(X1,X0)) = k1_waybel_9(X1,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_779,plain,
    ( ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | k5_yellow_2(X0,u1_waybel_0(X0,X1)) = k1_waybel_9(X0,X1)
    | sK5 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_25])).

cnf(c_780,plain,
    ( ~ l1_orders_2(sK3)
    | v2_struct_0(sK3)
    | k5_yellow_2(sK3,u1_waybel_0(sK3,sK5)) = k1_waybel_9(sK3,sK5) ),
    inference(unflattening,[status(thm)],[c_779])).

cnf(c_782,plain,
    ( k5_yellow_2(sK3,u1_waybel_0(sK3,sK5)) = k1_waybel_9(sK3,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_780,c_33,c_30,c_74,c_110])).

cnf(c_2127,plain,
    ( k5_yellow_2(sK3,u1_waybel_0(sK3,sK5)) = k1_waybel_9(sK3,sK5) ),
    inference(subtyping,[status(esa)],[c_782])).

cnf(c_3146,plain,
    ( k2_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = k1_waybel_9(sK3,sK5) ),
    inference(light_normalisation,[status(thm)],[c_3145,c_2127])).

cnf(c_3289,plain,
    ( k1_waybel_9(sK3,sK5) = X0_67
    | r1_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_67) != iProver_top
    | r1_orders_2(sK3,sK0(sK3,X0_67,k2_relat_1(u1_waybel_0(sK3,sK5))),sK4) = iProver_top
    | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK0(sK3,X0_67,k2_relat_1(u1_waybel_0(sK3,sK5))),u1_struct_0(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3096,c_3146])).

cnf(c_3299,plain,
    ( k1_waybel_9(sK3,sK5) = X0_67
    | k2_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = X0_67
    | r1_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_67) != iProver_top
    | r1_orders_2(sK3,sK0(sK3,X0_67,k2_relat_1(u1_waybel_0(sK3,sK5))),sK4) = iProver_top
    | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2572,c_3289])).

cnf(c_3305,plain,
    ( k1_waybel_9(sK3,sK5) = X0_67
    | r1_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_67) != iProver_top
    | r1_orders_2(sK3,sK0(sK3,X0_67,k2_relat_1(u1_waybel_0(sK3,sK5))),sK4) = iProver_top
    | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3299,c_3146])).

cnf(c_7,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK0(X0,X2,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1067,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK0(X0,X2,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,X1) = X2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_34])).

cnf(c_1068,plain,
    ( ~ r1_lattice3(sK3,X0,X1)
    | ~ r1_orders_2(sK3,sK0(sK3,X1,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | k2_yellow_0(sK3,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1067])).

cnf(c_1072,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r1_orders_2(sK3,sK0(sK3,X1,X0),X1)
    | ~ r1_lattice3(sK3,X0,X1)
    | k2_yellow_0(sK3,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1068,c_30,c_74])).

cnf(c_1073,plain,
    ( ~ r1_lattice3(sK3,X0,X1)
    | ~ r1_orders_2(sK3,sK0(sK3,X1,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k2_yellow_0(sK3,X0) = X1 ),
    inference(renaming,[status(thm)],[c_1072])).

cnf(c_2116,plain,
    ( ~ r1_lattice3(sK3,X0_69,X0_67)
    | ~ r1_orders_2(sK3,sK0(sK3,X0_67,X0_69),X0_67)
    | ~ m1_subset_1(X0_67,u1_struct_0(sK3))
    | k2_yellow_0(sK3,X0_69) = X0_67 ),
    inference(subtyping,[status(esa)],[c_1073])).

cnf(c_2574,plain,
    ( k2_yellow_0(sK3,X0_69) = X0_67
    | r1_lattice3(sK3,X0_69,X0_67) != iProver_top
    | r1_orders_2(sK3,sK0(sK3,X0_67,X0_69),X0_67) != iProver_top
    | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2116])).

cnf(c_3507,plain,
    ( k1_waybel_9(sK3,sK5) = sK4
    | k2_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = sK4
    | r1_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),sK4) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3305,c_2574])).

cnf(c_3512,plain,
    ( k1_waybel_9(sK3,sK5) = sK4
    | r1_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),sK4) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3507,c_3146])).

cnf(c_17,plain,
    ( ~ v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0)
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
    inference(cnf_transformation,[],[f90])).

cnf(c_23,negated_conjecture,
    ( v11_waybel_0(sK5,sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_501,plain,
    ( ~ v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0)
    | ~ r3_waybel_9(X0,X1,X2)
    | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
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
    | v2_struct_0(X1)
    | sK5 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_23])).

cnf(c_502,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK3,sK1(sK3)),sK3,sK3)
    | ~ r3_waybel_9(sK3,sK5,X0)
    | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | ~ l1_waybel_0(sK5,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ v2_pre_topc(sK3)
    | ~ v8_pre_topc(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v2_lattice3(sK3)
    | ~ v1_compts_1(sK3)
    | ~ v4_orders_2(sK5)
    | ~ v4_orders_2(sK3)
    | ~ v7_waybel_0(sK5)
    | ~ l1_waybel_9(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v1_lattice3(sK3)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_501])).

cnf(c_506,plain,
    ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | ~ r3_waybel_9(sK3,sK5,X0)
    | ~ v5_pre_topc(k4_waybel_1(sK3,sK1(sK3)),sK3,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_502,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_31,c_30,c_28,c_27,c_26,c_25])).

cnf(c_507,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK3,sK1(sK3)),sK3,sK3)
    | ~ r3_waybel_9(sK3,sK5,X0)
    | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_506])).

cnf(c_580,plain,
    ( ~ r3_waybel_9(sK3,sK5,X0)
    | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X1)
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_507])).

cnf(c_918,plain,
    ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X1)
    | sK4 != X0
    | sK5 != sK5
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_580])).

cnf(c_919,plain,
    ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_918])).

cnf(c_923,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
    | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_919,c_29])).

cnf(c_924,plain,
    ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0) ),
    inference(renaming,[status(thm)],[c_923])).

cnf(c_2122,plain,
    ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
    | ~ m1_subset_1(X0_67,u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0_67) ),
    inference(subtyping,[status(esa)],[c_924])).

cnf(c_2568,plain,
    ( k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0_67)
    | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) = iProver_top
    | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2122])).

cnf(c_18,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
    | ~ v11_waybel_0(X1,X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0),u1_struct_0(X0))
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
    inference(cnf_transformation,[],[f91])).

cnf(c_477,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0),u1_struct_0(X0))
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
    | sK5 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_23])).

cnf(c_478,plain,
    ( ~ r3_waybel_9(sK3,sK5,X0)
    | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | ~ l1_waybel_0(sK5,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3),u1_struct_0(sK3))
    | ~ v2_pre_topc(sK3)
    | ~ v8_pre_topc(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v2_lattice3(sK3)
    | ~ v1_compts_1(sK3)
    | ~ v4_orders_2(sK5)
    | ~ v4_orders_2(sK3)
    | ~ v7_waybel_0(sK5)
    | ~ l1_waybel_9(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v1_lattice3(sK3)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_477])).

cnf(c_482,plain,
    ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | ~ r3_waybel_9(sK3,sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_478,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_31,c_30,c_28,c_27,c_26,c_25])).

cnf(c_483,plain,
    ( ~ r3_waybel_9(sK3,sK5,X0)
    | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_482])).

cnf(c_939,plain,
    ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3),u1_struct_0(sK3))
    | sK4 != X0
    | sK5 != sK5
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_483])).

cnf(c_940,plain,
    ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
    | m1_subset_1(sK1(sK3),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_939])).

cnf(c_942,plain,
    ( m1_subset_1(sK1(sK3),u1_struct_0(sK3))
    | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_940,c_29])).

cnf(c_943,plain,
    ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
    | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_942])).

cnf(c_944,plain,
    ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) = iProver_top
    | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_943])).

cnf(c_2140,plain,
    ( X0_71 = X0_71 ),
    theory(equality)).

cnf(c_2755,plain,
    ( k4_waybel_1(sK3,sK1(sK3)) = k4_waybel_1(sK3,sK1(sK3)) ),
    inference(instantiation,[status(thm)],[c_2140])).

cnf(c_2756,plain,
    ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
    | ~ m1_subset_1(sK1(sK3),u1_struct_0(sK3))
    | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,sK1(sK3)) ),
    inference(instantiation,[status(thm)],[c_2122])).

cnf(c_2757,plain,
    ( k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,sK1(sK3))
    | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) = iProver_top
    | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2756])).

cnf(c_2795,plain,
    ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2568,c_944,c_2755,c_2757])).

cnf(c_2875,plain,
    ( r1_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2822,c_2795])).

cnf(c_21,negated_conjecture,
    ( k1_waybel_9(sK3,sK5) != sK4 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2129,negated_conjecture,
    ( k1_waybel_9(sK3,sK5) != sK4 ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_48,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3512,c_2875,c_2129,c_48])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:48:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.87/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/0.98  
% 1.87/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.87/0.98  
% 1.87/0.98  ------  iProver source info
% 1.87/0.98  
% 1.87/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.87/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.87/0.98  git: non_committed_changes: false
% 1.87/0.98  git: last_make_outside_of_git: false
% 1.87/0.98  
% 1.87/0.98  ------ 
% 1.87/0.98  
% 1.87/0.98  ------ Input Options
% 1.87/0.98  
% 1.87/0.98  --out_options                           all
% 1.87/0.98  --tptp_safe_out                         true
% 1.87/0.98  --problem_path                          ""
% 1.87/0.98  --include_path                          ""
% 1.87/0.98  --clausifier                            res/vclausify_rel
% 1.87/0.98  --clausifier_options                    --mode clausify
% 1.87/0.98  --stdin                                 false
% 1.87/0.98  --stats_out                             all
% 1.87/0.98  
% 1.87/0.98  ------ General Options
% 1.87/0.98  
% 1.87/0.98  --fof                                   false
% 1.87/0.98  --time_out_real                         305.
% 1.87/0.98  --time_out_virtual                      -1.
% 1.87/0.98  --symbol_type_check                     false
% 1.87/0.98  --clausify_out                          false
% 1.87/0.98  --sig_cnt_out                           false
% 1.87/0.98  --trig_cnt_out                          false
% 1.87/0.98  --trig_cnt_out_tolerance                1.
% 1.87/0.98  --trig_cnt_out_sk_spl                   false
% 1.87/0.98  --abstr_cl_out                          false
% 1.87/0.98  
% 1.87/0.98  ------ Global Options
% 1.87/0.98  
% 1.87/0.98  --schedule                              default
% 1.87/0.98  --add_important_lit                     false
% 1.87/0.98  --prop_solver_per_cl                    1000
% 1.87/0.98  --min_unsat_core                        false
% 1.87/0.98  --soft_assumptions                      false
% 1.87/0.98  --soft_lemma_size                       3
% 1.87/0.98  --prop_impl_unit_size                   0
% 1.87/0.98  --prop_impl_unit                        []
% 1.87/0.98  --share_sel_clauses                     true
% 1.87/0.98  --reset_solvers                         false
% 1.87/0.98  --bc_imp_inh                            [conj_cone]
% 1.87/0.98  --conj_cone_tolerance                   3.
% 1.87/0.98  --extra_neg_conj                        none
% 1.87/0.98  --large_theory_mode                     true
% 1.87/0.98  --prolific_symb_bound                   200
% 1.87/0.98  --lt_threshold                          2000
% 1.87/0.98  --clause_weak_htbl                      true
% 1.87/0.98  --gc_record_bc_elim                     false
% 1.87/0.98  
% 1.87/0.98  ------ Preprocessing Options
% 1.87/0.98  
% 1.87/0.98  --preprocessing_flag                    true
% 1.87/0.98  --time_out_prep_mult                    0.1
% 1.87/0.98  --splitting_mode                        input
% 1.87/0.98  --splitting_grd                         true
% 1.87/0.98  --splitting_cvd                         false
% 1.87/0.98  --splitting_cvd_svl                     false
% 1.87/0.98  --splitting_nvd                         32
% 1.87/0.98  --sub_typing                            true
% 1.87/0.98  --prep_gs_sim                           true
% 1.87/0.98  --prep_unflatten                        true
% 1.87/0.98  --prep_res_sim                          true
% 1.87/0.98  --prep_upred                            true
% 1.87/0.98  --prep_sem_filter                       exhaustive
% 1.87/0.98  --prep_sem_filter_out                   false
% 1.87/0.98  --pred_elim                             true
% 1.87/0.98  --res_sim_input                         true
% 1.87/0.98  --eq_ax_congr_red                       true
% 1.87/0.98  --pure_diseq_elim                       true
% 1.87/0.98  --brand_transform                       false
% 1.87/0.98  --non_eq_to_eq                          false
% 1.87/0.98  --prep_def_merge                        true
% 1.87/0.98  --prep_def_merge_prop_impl              false
% 1.87/0.98  --prep_def_merge_mbd                    true
% 1.87/0.98  --prep_def_merge_tr_red                 false
% 1.87/0.98  --prep_def_merge_tr_cl                  false
% 1.87/0.98  --smt_preprocessing                     true
% 1.87/0.98  --smt_ac_axioms                         fast
% 1.87/0.98  --preprocessed_out                      false
% 1.87/0.98  --preprocessed_stats                    false
% 1.87/0.98  
% 1.87/0.98  ------ Abstraction refinement Options
% 1.87/0.98  
% 1.87/0.98  --abstr_ref                             []
% 1.87/0.98  --abstr_ref_prep                        false
% 1.87/0.98  --abstr_ref_until_sat                   false
% 1.87/0.98  --abstr_ref_sig_restrict                funpre
% 1.87/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.87/0.98  --abstr_ref_under                       []
% 1.87/0.98  
% 1.87/0.98  ------ SAT Options
% 1.87/0.98  
% 1.87/0.98  --sat_mode                              false
% 1.87/0.98  --sat_fm_restart_options                ""
% 1.87/0.98  --sat_gr_def                            false
% 1.87/0.98  --sat_epr_types                         true
% 1.87/0.98  --sat_non_cyclic_types                  false
% 1.87/0.98  --sat_finite_models                     false
% 1.87/0.98  --sat_fm_lemmas                         false
% 1.87/0.98  --sat_fm_prep                           false
% 1.87/0.98  --sat_fm_uc_incr                        true
% 1.87/0.98  --sat_out_model                         small
% 1.87/0.98  --sat_out_clauses                       false
% 1.87/0.98  
% 1.87/0.98  ------ QBF Options
% 1.87/0.98  
% 1.87/0.98  --qbf_mode                              false
% 1.87/0.98  --qbf_elim_univ                         false
% 1.87/0.98  --qbf_dom_inst                          none
% 1.87/0.98  --qbf_dom_pre_inst                      false
% 1.87/0.98  --qbf_sk_in                             false
% 1.87/0.98  --qbf_pred_elim                         true
% 1.87/0.98  --qbf_split                             512
% 1.87/0.98  
% 1.87/0.98  ------ BMC1 Options
% 1.87/0.98  
% 1.87/0.98  --bmc1_incremental                      false
% 1.87/0.98  --bmc1_axioms                           reachable_all
% 1.87/0.98  --bmc1_min_bound                        0
% 1.87/0.98  --bmc1_max_bound                        -1
% 1.87/0.98  --bmc1_max_bound_default                -1
% 1.87/0.98  --bmc1_symbol_reachability              true
% 1.87/0.98  --bmc1_property_lemmas                  false
% 1.87/0.98  --bmc1_k_induction                      false
% 1.87/0.98  --bmc1_non_equiv_states                 false
% 1.87/0.98  --bmc1_deadlock                         false
% 1.87/0.98  --bmc1_ucm                              false
% 1.87/0.98  --bmc1_add_unsat_core                   none
% 1.87/0.98  --bmc1_unsat_core_children              false
% 1.87/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.87/0.98  --bmc1_out_stat                         full
% 1.87/0.98  --bmc1_ground_init                      false
% 1.87/0.98  --bmc1_pre_inst_next_state              false
% 1.87/0.98  --bmc1_pre_inst_state                   false
% 1.87/0.98  --bmc1_pre_inst_reach_state             false
% 1.87/0.98  --bmc1_out_unsat_core                   false
% 1.87/0.98  --bmc1_aig_witness_out                  false
% 1.87/0.98  --bmc1_verbose                          false
% 1.87/0.98  --bmc1_dump_clauses_tptp                false
% 1.87/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.87/0.98  --bmc1_dump_file                        -
% 1.87/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.87/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.87/0.98  --bmc1_ucm_extend_mode                  1
% 1.87/0.98  --bmc1_ucm_init_mode                    2
% 1.87/0.98  --bmc1_ucm_cone_mode                    none
% 1.87/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.87/0.98  --bmc1_ucm_relax_model                  4
% 1.87/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.87/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.87/0.98  --bmc1_ucm_layered_model                none
% 1.87/0.98  --bmc1_ucm_max_lemma_size               10
% 1.87/0.98  
% 1.87/0.98  ------ AIG Options
% 1.87/0.98  
% 1.87/0.98  --aig_mode                              false
% 1.87/0.98  
% 1.87/0.98  ------ Instantiation Options
% 1.87/0.98  
% 1.87/0.98  --instantiation_flag                    true
% 1.87/0.98  --inst_sos_flag                         false
% 1.87/0.98  --inst_sos_phase                        true
% 1.87/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.87/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.87/0.98  --inst_lit_sel_side                     num_symb
% 1.87/0.98  --inst_solver_per_active                1400
% 1.87/0.98  --inst_solver_calls_frac                1.
% 1.87/0.98  --inst_passive_queue_type               priority_queues
% 1.87/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.87/0.98  --inst_passive_queues_freq              [25;2]
% 1.87/0.98  --inst_dismatching                      true
% 1.87/0.98  --inst_eager_unprocessed_to_passive     true
% 1.87/0.98  --inst_prop_sim_given                   true
% 1.87/0.98  --inst_prop_sim_new                     false
% 1.87/0.98  --inst_subs_new                         false
% 1.87/0.99  --inst_eq_res_simp                      false
% 1.87/0.99  --inst_subs_given                       false
% 1.87/0.99  --inst_orphan_elimination               true
% 1.87/0.99  --inst_learning_loop_flag               true
% 1.87/0.99  --inst_learning_start                   3000
% 1.87/0.99  --inst_learning_factor                  2
% 1.87/0.99  --inst_start_prop_sim_after_learn       3
% 1.87/0.99  --inst_sel_renew                        solver
% 1.87/0.99  --inst_lit_activity_flag                true
% 1.87/0.99  --inst_restr_to_given                   false
% 1.87/0.99  --inst_activity_threshold               500
% 1.87/0.99  --inst_out_proof                        true
% 1.87/0.99  
% 1.87/0.99  ------ Resolution Options
% 1.87/0.99  
% 1.87/0.99  --resolution_flag                       true
% 1.87/0.99  --res_lit_sel                           adaptive
% 1.87/0.99  --res_lit_sel_side                      none
% 1.87/0.99  --res_ordering                          kbo
% 1.87/0.99  --res_to_prop_solver                    active
% 1.87/0.99  --res_prop_simpl_new                    false
% 1.87/0.99  --res_prop_simpl_given                  true
% 1.87/0.99  --res_passive_queue_type                priority_queues
% 1.87/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.87/0.99  --res_passive_queues_freq               [15;5]
% 1.87/0.99  --res_forward_subs                      full
% 1.87/0.99  --res_backward_subs                     full
% 1.87/0.99  --res_forward_subs_resolution           true
% 1.87/0.99  --res_backward_subs_resolution          true
% 1.87/0.99  --res_orphan_elimination                true
% 1.87/0.99  --res_time_limit                        2.
% 1.87/0.99  --res_out_proof                         true
% 1.87/0.99  
% 1.87/0.99  ------ Superposition Options
% 1.87/0.99  
% 1.87/0.99  --superposition_flag                    true
% 1.87/0.99  --sup_passive_queue_type                priority_queues
% 1.87/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.87/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.87/0.99  --demod_completeness_check              fast
% 1.87/0.99  --demod_use_ground                      true
% 1.87/0.99  --sup_to_prop_solver                    passive
% 1.87/0.99  --sup_prop_simpl_new                    true
% 1.87/0.99  --sup_prop_simpl_given                  true
% 1.87/0.99  --sup_fun_splitting                     false
% 1.87/0.99  --sup_smt_interval                      50000
% 1.87/0.99  
% 1.87/0.99  ------ Superposition Simplification Setup
% 1.87/0.99  
% 1.87/0.99  --sup_indices_passive                   []
% 1.87/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.87/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/0.99  --sup_full_bw                           [BwDemod]
% 1.87/0.99  --sup_immed_triv                        [TrivRules]
% 1.87/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.87/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/0.99  --sup_immed_bw_main                     []
% 1.87/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.87/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.87/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.87/0.99  
% 1.87/0.99  ------ Combination Options
% 1.87/0.99  
% 1.87/0.99  --comb_res_mult                         3
% 1.87/0.99  --comb_sup_mult                         2
% 1.87/0.99  --comb_inst_mult                        10
% 1.87/0.99  
% 1.87/0.99  ------ Debug Options
% 1.87/0.99  
% 1.87/0.99  --dbg_backtrace                         false
% 1.87/0.99  --dbg_dump_prop_clauses                 false
% 1.87/0.99  --dbg_dump_prop_clauses_file            -
% 1.87/0.99  --dbg_out_stat                          false
% 1.87/0.99  ------ Parsing...
% 1.87/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.87/0.99  
% 1.87/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe:16:0s pe_e  sf_s  rm: 16 0s  sf_e  pe_s  pe_e 
% 1.87/0.99  
% 1.87/0.99  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.87/0.99  
% 1.87/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.87/0.99  ------ Proving...
% 1.87/0.99  ------ Problem Properties 
% 1.87/0.99  
% 1.87/0.99  
% 1.87/0.99  clauses                                 22
% 1.87/0.99  conjectures                             2
% 1.87/0.99  EPR                                     1
% 1.87/0.99  Horn                                    15
% 1.87/0.99  unary                                   4
% 1.87/0.99  binary                                  5
% 1.87/0.99  lits                                    63
% 1.87/0.99  lits eq                                 11
% 1.87/0.99  fd_pure                                 0
% 1.87/0.99  fd_pseudo                               0
% 1.87/0.99  fd_cond                                 0
% 1.87/0.99  fd_pseudo_cond                          3
% 1.87/0.99  AC symbols                              0
% 1.87/0.99  
% 1.87/0.99  ------ Schedule dynamic 5 is on 
% 1.87/0.99  
% 1.87/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.87/0.99  
% 1.87/0.99  
% 1.87/0.99  ------ 
% 1.87/0.99  Current options:
% 1.87/0.99  ------ 
% 1.87/0.99  
% 1.87/0.99  ------ Input Options
% 1.87/0.99  
% 1.87/0.99  --out_options                           all
% 1.87/0.99  --tptp_safe_out                         true
% 1.87/0.99  --problem_path                          ""
% 1.87/0.99  --include_path                          ""
% 1.87/0.99  --clausifier                            res/vclausify_rel
% 1.87/0.99  --clausifier_options                    --mode clausify
% 1.87/0.99  --stdin                                 false
% 1.87/0.99  --stats_out                             all
% 1.87/0.99  
% 1.87/0.99  ------ General Options
% 1.87/0.99  
% 1.87/0.99  --fof                                   false
% 1.87/0.99  --time_out_real                         305.
% 1.87/0.99  --time_out_virtual                      -1.
% 1.87/0.99  --symbol_type_check                     false
% 1.87/0.99  --clausify_out                          false
% 1.87/0.99  --sig_cnt_out                           false
% 1.87/0.99  --trig_cnt_out                          false
% 1.87/0.99  --trig_cnt_out_tolerance                1.
% 1.87/0.99  --trig_cnt_out_sk_spl                   false
% 1.87/0.99  --abstr_cl_out                          false
% 1.87/0.99  
% 1.87/0.99  ------ Global Options
% 1.87/0.99  
% 1.87/0.99  --schedule                              default
% 1.87/0.99  --add_important_lit                     false
% 1.87/0.99  --prop_solver_per_cl                    1000
% 1.87/0.99  --min_unsat_core                        false
% 1.87/0.99  --soft_assumptions                      false
% 1.87/0.99  --soft_lemma_size                       3
% 1.87/0.99  --prop_impl_unit_size                   0
% 1.87/0.99  --prop_impl_unit                        []
% 1.87/0.99  --share_sel_clauses                     true
% 1.87/0.99  --reset_solvers                         false
% 1.87/0.99  --bc_imp_inh                            [conj_cone]
% 1.87/0.99  --conj_cone_tolerance                   3.
% 1.87/0.99  --extra_neg_conj                        none
% 1.87/0.99  --large_theory_mode                     true
% 1.87/0.99  --prolific_symb_bound                   200
% 1.87/0.99  --lt_threshold                          2000
% 1.87/0.99  --clause_weak_htbl                      true
% 1.87/0.99  --gc_record_bc_elim                     false
% 1.87/0.99  
% 1.87/0.99  ------ Preprocessing Options
% 1.87/0.99  
% 1.87/0.99  --preprocessing_flag                    true
% 1.87/0.99  --time_out_prep_mult                    0.1
% 1.87/0.99  --splitting_mode                        input
% 1.87/0.99  --splitting_grd                         true
% 1.87/0.99  --splitting_cvd                         false
% 1.87/0.99  --splitting_cvd_svl                     false
% 1.87/0.99  --splitting_nvd                         32
% 1.87/0.99  --sub_typing                            true
% 1.87/0.99  --prep_gs_sim                           true
% 1.87/0.99  --prep_unflatten                        true
% 1.87/0.99  --prep_res_sim                          true
% 1.87/0.99  --prep_upred                            true
% 1.87/0.99  --prep_sem_filter                       exhaustive
% 1.87/0.99  --prep_sem_filter_out                   false
% 1.87/0.99  --pred_elim                             true
% 1.87/0.99  --res_sim_input                         true
% 1.87/0.99  --eq_ax_congr_red                       true
% 1.87/0.99  --pure_diseq_elim                       true
% 1.87/0.99  --brand_transform                       false
% 1.87/0.99  --non_eq_to_eq                          false
% 1.87/0.99  --prep_def_merge                        true
% 1.87/0.99  --prep_def_merge_prop_impl              false
% 1.87/0.99  --prep_def_merge_mbd                    true
% 1.87/0.99  --prep_def_merge_tr_red                 false
% 1.87/0.99  --prep_def_merge_tr_cl                  false
% 1.87/0.99  --smt_preprocessing                     true
% 1.87/0.99  --smt_ac_axioms                         fast
% 1.87/0.99  --preprocessed_out                      false
% 1.87/0.99  --preprocessed_stats                    false
% 1.87/0.99  
% 1.87/0.99  ------ Abstraction refinement Options
% 1.87/0.99  
% 1.87/0.99  --abstr_ref                             []
% 1.87/0.99  --abstr_ref_prep                        false
% 1.87/0.99  --abstr_ref_until_sat                   false
% 1.87/0.99  --abstr_ref_sig_restrict                funpre
% 1.87/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.87/0.99  --abstr_ref_under                       []
% 1.87/0.99  
% 1.87/0.99  ------ SAT Options
% 1.87/0.99  
% 1.87/0.99  --sat_mode                              false
% 1.87/0.99  --sat_fm_restart_options                ""
% 1.87/0.99  --sat_gr_def                            false
% 1.87/0.99  --sat_epr_types                         true
% 1.87/0.99  --sat_non_cyclic_types                  false
% 1.87/0.99  --sat_finite_models                     false
% 1.87/0.99  --sat_fm_lemmas                         false
% 1.87/0.99  --sat_fm_prep                           false
% 1.87/0.99  --sat_fm_uc_incr                        true
% 1.87/0.99  --sat_out_model                         small
% 1.87/0.99  --sat_out_clauses                       false
% 1.87/0.99  
% 1.87/0.99  ------ QBF Options
% 1.87/0.99  
% 1.87/0.99  --qbf_mode                              false
% 1.87/0.99  --qbf_elim_univ                         false
% 1.87/0.99  --qbf_dom_inst                          none
% 1.87/0.99  --qbf_dom_pre_inst                      false
% 1.87/0.99  --qbf_sk_in                             false
% 1.87/0.99  --qbf_pred_elim                         true
% 1.87/0.99  --qbf_split                             512
% 1.87/0.99  
% 1.87/0.99  ------ BMC1 Options
% 1.87/0.99  
% 1.87/0.99  --bmc1_incremental                      false
% 1.87/0.99  --bmc1_axioms                           reachable_all
% 1.87/0.99  --bmc1_min_bound                        0
% 1.87/0.99  --bmc1_max_bound                        -1
% 1.87/0.99  --bmc1_max_bound_default                -1
% 1.87/0.99  --bmc1_symbol_reachability              true
% 1.87/0.99  --bmc1_property_lemmas                  false
% 1.87/0.99  --bmc1_k_induction                      false
% 1.87/0.99  --bmc1_non_equiv_states                 false
% 1.87/0.99  --bmc1_deadlock                         false
% 1.87/0.99  --bmc1_ucm                              false
% 1.87/0.99  --bmc1_add_unsat_core                   none
% 1.87/0.99  --bmc1_unsat_core_children              false
% 1.87/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.87/0.99  --bmc1_out_stat                         full
% 1.87/0.99  --bmc1_ground_init                      false
% 1.87/0.99  --bmc1_pre_inst_next_state              false
% 1.87/0.99  --bmc1_pre_inst_state                   false
% 1.87/0.99  --bmc1_pre_inst_reach_state             false
% 1.87/0.99  --bmc1_out_unsat_core                   false
% 1.87/0.99  --bmc1_aig_witness_out                  false
% 1.87/0.99  --bmc1_verbose                          false
% 1.87/0.99  --bmc1_dump_clauses_tptp                false
% 1.87/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.87/0.99  --bmc1_dump_file                        -
% 1.87/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.87/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.87/0.99  --bmc1_ucm_extend_mode                  1
% 1.87/0.99  --bmc1_ucm_init_mode                    2
% 1.87/0.99  --bmc1_ucm_cone_mode                    none
% 1.87/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.87/0.99  --bmc1_ucm_relax_model                  4
% 1.87/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.87/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.87/0.99  --bmc1_ucm_layered_model                none
% 1.87/0.99  --bmc1_ucm_max_lemma_size               10
% 1.87/0.99  
% 1.87/0.99  ------ AIG Options
% 1.87/0.99  
% 1.87/0.99  --aig_mode                              false
% 1.87/0.99  
% 1.87/0.99  ------ Instantiation Options
% 1.87/0.99  
% 1.87/0.99  --instantiation_flag                    true
% 1.87/0.99  --inst_sos_flag                         false
% 1.87/0.99  --inst_sos_phase                        true
% 1.87/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.87/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.87/0.99  --inst_lit_sel_side                     none
% 1.87/0.99  --inst_solver_per_active                1400
% 1.87/0.99  --inst_solver_calls_frac                1.
% 1.87/0.99  --inst_passive_queue_type               priority_queues
% 1.87/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.87/0.99  --inst_passive_queues_freq              [25;2]
% 1.87/0.99  --inst_dismatching                      true
% 1.87/0.99  --inst_eager_unprocessed_to_passive     true
% 1.87/0.99  --inst_prop_sim_given                   true
% 1.87/0.99  --inst_prop_sim_new                     false
% 1.87/0.99  --inst_subs_new                         false
% 1.87/0.99  --inst_eq_res_simp                      false
% 1.87/0.99  --inst_subs_given                       false
% 1.87/0.99  --inst_orphan_elimination               true
% 1.87/0.99  --inst_learning_loop_flag               true
% 1.87/0.99  --inst_learning_start                   3000
% 1.87/0.99  --inst_learning_factor                  2
% 1.87/0.99  --inst_start_prop_sim_after_learn       3
% 1.87/0.99  --inst_sel_renew                        solver
% 1.87/0.99  --inst_lit_activity_flag                true
% 1.87/0.99  --inst_restr_to_given                   false
% 1.87/0.99  --inst_activity_threshold               500
% 1.87/0.99  --inst_out_proof                        true
% 1.87/0.99  
% 1.87/0.99  ------ Resolution Options
% 1.87/0.99  
% 1.87/0.99  --resolution_flag                       false
% 1.87/0.99  --res_lit_sel                           adaptive
% 1.87/0.99  --res_lit_sel_side                      none
% 1.87/0.99  --res_ordering                          kbo
% 1.87/0.99  --res_to_prop_solver                    active
% 1.87/0.99  --res_prop_simpl_new                    false
% 1.87/0.99  --res_prop_simpl_given                  true
% 1.87/0.99  --res_passive_queue_type                priority_queues
% 1.87/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.87/0.99  --res_passive_queues_freq               [15;5]
% 1.87/0.99  --res_forward_subs                      full
% 1.87/0.99  --res_backward_subs                     full
% 1.87/0.99  --res_forward_subs_resolution           true
% 1.87/0.99  --res_backward_subs_resolution          true
% 1.87/0.99  --res_orphan_elimination                true
% 1.87/0.99  --res_time_limit                        2.
% 1.87/0.99  --res_out_proof                         true
% 1.87/0.99  
% 1.87/0.99  ------ Superposition Options
% 1.87/0.99  
% 1.87/0.99  --superposition_flag                    true
% 1.87/0.99  --sup_passive_queue_type                priority_queues
% 1.87/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.87/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.87/0.99  --demod_completeness_check              fast
% 1.87/0.99  --demod_use_ground                      true
% 1.87/0.99  --sup_to_prop_solver                    passive
% 1.87/0.99  --sup_prop_simpl_new                    true
% 1.87/0.99  --sup_prop_simpl_given                  true
% 1.87/0.99  --sup_fun_splitting                     false
% 1.87/0.99  --sup_smt_interval                      50000
% 1.87/0.99  
% 1.87/0.99  ------ Superposition Simplification Setup
% 1.87/0.99  
% 1.87/0.99  --sup_indices_passive                   []
% 1.87/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.87/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/0.99  --sup_full_bw                           [BwDemod]
% 1.87/0.99  --sup_immed_triv                        [TrivRules]
% 1.87/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.87/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/0.99  --sup_immed_bw_main                     []
% 1.87/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.87/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.87/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.87/0.99  
% 1.87/0.99  ------ Combination Options
% 1.87/0.99  
% 1.87/0.99  --comb_res_mult                         3
% 1.87/0.99  --comb_sup_mult                         2
% 1.87/0.99  --comb_inst_mult                        10
% 1.87/0.99  
% 1.87/0.99  ------ Debug Options
% 1.87/0.99  
% 1.87/0.99  --dbg_backtrace                         false
% 1.87/0.99  --dbg_dump_prop_clauses                 false
% 1.87/0.99  --dbg_dump_prop_clauses_file            -
% 1.87/0.99  --dbg_out_stat                          false
% 1.87/0.99  
% 1.87/0.99  
% 1.87/0.99  
% 1.87/0.99  
% 1.87/0.99  ------ Proving...
% 1.87/0.99  
% 1.87/0.99  
% 1.87/0.99  % SZS status Theorem for theBenchmark.p
% 1.87/0.99  
% 1.87/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.87/0.99  
% 1.87/0.99  fof(f5,axiom,(
% 1.87/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1)) => (r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1)) & ((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1))))))),
% 1.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f14,plain,(
% 1.87/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1)) => (r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1)) & ((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X4) => r1_orders_2(X0,X4,X1))) & r1_lattice3(X0,X2,X1))))))),
% 1.87/0.99    inference(rectify,[],[f5])).
% 1.87/0.99  
% 1.87/0.99  fof(f23,plain,(
% 1.87/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | (~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 1.87/0.99    inference(ennf_transformation,[],[f14])).
% 1.87/0.99  
% 1.87/0.99  fof(f24,plain,(
% 1.87/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | ~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 1.87/0.99    inference(flattening,[],[f23])).
% 1.87/0.99  
% 1.87/0.99  fof(f38,plain,(
% 1.87/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK0(X0,X1,X2),X1) & r1_lattice3(X0,X2,sK0(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 1.87/0.99    introduced(choice_axiom,[])).
% 1.87/0.99  
% 1.87/0.99  fof(f39,plain,(
% 1.87/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) | (~r1_orders_2(X0,sK0(X0,X1,X2),X1) & r1_lattice3(X0,X2,sK0(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | ~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 1.87/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f38])).
% 1.87/0.99  
% 1.87/0.99  fof(f55,plain,(
% 1.87/0.99    ( ! [X2,X0,X1] : (k2_yellow_0(X0,X2) = X1 | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f39])).
% 1.87/0.99  
% 1.87/0.99  fof(f12,conjecture,(
% 1.87/0.99    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => ((r3_waybel_9(X0,X2,X1) & v11_waybel_0(X2,X0) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0))) => k1_waybel_9(X0,X2) = X1))))),
% 1.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f13,negated_conjecture,(
% 1.87/0.99    ~! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => ((r3_waybel_9(X0,X2,X1) & v11_waybel_0(X2,X0) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0))) => k1_waybel_9(X0,X2) = X1))))),
% 1.87/0.99    inference(negated_conjecture,[],[f12])).
% 1.87/0.99  
% 1.87/0.99  fof(f36,plain,(
% 1.87/0.99    ? [X0] : (? [X1] : (? [X2] : ((k1_waybel_9(X0,X2) != X1 & (r3_waybel_9(X0,X2,X1) & v11_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))))) & (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.87/0.99    inference(ennf_transformation,[],[f13])).
% 1.87/0.99  
% 1.87/0.99  fof(f37,plain,(
% 1.87/0.99    ? [X0] : (? [X1] : (? [X2] : (k1_waybel_9(X0,X2) != X1 & r3_waybel_9(X0,X2,X1) & v11_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 1.87/0.99    inference(flattening,[],[f36])).
% 1.87/0.99  
% 1.87/0.99  fof(f47,plain,(
% 1.87/0.99    ( ! [X0,X1] : (? [X2] : (k1_waybel_9(X0,X2) != X1 & r3_waybel_9(X0,X2,X1) & v11_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (k1_waybel_9(X0,sK5) != X1 & r3_waybel_9(X0,sK5,X1) & v11_waybel_0(sK5,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(sK5,X0) & v7_waybel_0(sK5) & v4_orders_2(sK5) & ~v2_struct_0(sK5))) )),
% 1.87/0.99    introduced(choice_axiom,[])).
% 1.87/0.99  
% 1.87/0.99  fof(f46,plain,(
% 1.87/0.99    ( ! [X0] : (? [X1] : (? [X2] : (k1_waybel_9(X0,X2) != X1 & r3_waybel_9(X0,X2,X1) & v11_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_waybel_9(X0,X2) != sK4 & r3_waybel_9(X0,X2,sK4) & v11_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 1.87/0.99    introduced(choice_axiom,[])).
% 1.87/0.99  
% 1.87/0.99  fof(f45,plain,(
% 1.87/0.99    ? [X0] : (? [X1] : (? [X2] : (k1_waybel_9(X0,X2) != X1 & r3_waybel_9(X0,X2,X1) & v11_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (k1_waybel_9(sK3,X2) != X1 & r3_waybel_9(sK3,X2,X1) & v11_waybel_0(X2,sK3) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK3,X3),sK3,sK3) | ~m1_subset_1(X3,u1_struct_0(sK3))) & l1_waybel_0(X2,sK3) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_waybel_9(sK3) & v1_compts_1(sK3) & v2_lattice3(sK3) & v1_lattice3(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & v8_pre_topc(sK3) & v2_pre_topc(sK3))),
% 1.87/0.99    introduced(choice_axiom,[])).
% 1.87/0.99  
% 1.87/0.99  fof(f48,plain,(
% 1.87/0.99    ((k1_waybel_9(sK3,sK5) != sK4 & r3_waybel_9(sK3,sK5,sK4) & v11_waybel_0(sK5,sK3) & ! [X3] : (v5_pre_topc(k4_waybel_1(sK3,X3),sK3,sK3) | ~m1_subset_1(X3,u1_struct_0(sK3))) & l1_waybel_0(sK5,sK3) & v7_waybel_0(sK5) & v4_orders_2(sK5) & ~v2_struct_0(sK5)) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_waybel_9(sK3) & v1_compts_1(sK3) & v2_lattice3(sK3) & v1_lattice3(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & v8_pre_topc(sK3) & v2_pre_topc(sK3)),
% 1.87/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f37,f47,f46,f45])).
% 1.87/0.99  
% 1.87/0.99  fof(f74,plain,(
% 1.87/0.99    v5_orders_2(sK3)),
% 1.87/0.99    inference(cnf_transformation,[],[f48])).
% 1.87/0.99  
% 1.87/0.99  fof(f78,plain,(
% 1.87/0.99    l1_waybel_9(sK3)),
% 1.87/0.99    inference(cnf_transformation,[],[f48])).
% 1.87/0.99  
% 1.87/0.99  fof(f9,axiom,(
% 1.87/0.99    ! [X0] : (l1_waybel_9(X0) => (l1_orders_2(X0) & l1_pre_topc(X0)))),
% 1.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f31,plain,(
% 1.87/0.99    ! [X0] : ((l1_orders_2(X0) & l1_pre_topc(X0)) | ~l1_waybel_9(X0))),
% 1.87/0.99    inference(ennf_transformation,[],[f9])).
% 1.87/0.99  
% 1.87/0.99  fof(f65,plain,(
% 1.87/0.99    ( ! [X0] : (l1_orders_2(X0) | ~l1_waybel_9(X0)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f31])).
% 1.87/0.99  
% 1.87/0.99  fof(f56,plain,(
% 1.87/0.99    ( ! [X2,X0,X1] : (k2_yellow_0(X0,X2) = X1 | r1_lattice3(X0,X2,sK0(X0,X1,X2)) | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f39])).
% 1.87/0.99  
% 1.87/0.99  fof(f86,plain,(
% 1.87/0.99    r3_waybel_9(sK3,sK5,sK4)),
% 1.87/0.99    inference(cnf_transformation,[],[f48])).
% 1.87/0.99  
% 1.87/0.99  fof(f82,plain,(
% 1.87/0.99    v7_waybel_0(sK5)),
% 1.87/0.99    inference(cnf_transformation,[],[f48])).
% 1.87/0.99  
% 1.87/0.99  fof(f11,axiom,(
% 1.87/0.99    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) => r1_orders_2(X0,X4,X3))))))))),
% 1.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f15,plain,(
% 1.87/0.99    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) => r1_orders_2(X0,X5,X3))))))))),
% 1.87/0.99    inference(rectify,[],[f11])).
% 1.87/0.99  
% 1.87/0.99  fof(f34,plain,(
% 1.87/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X5] : ((r1_orders_2(X0,X5,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)) | ~m1_subset_1(X5,u1_struct_0(X0))) | (~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.87/0.99    inference(ennf_transformation,[],[f15])).
% 1.87/0.99  
% 1.87/0.99  fof(f35,plain,(
% 1.87/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.87/0.99    inference(flattening,[],[f34])).
% 1.87/0.99  
% 1.87/0.99  fof(f42,plain,(
% 1.87/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | ? [X5] : (~v5_pre_topc(k4_waybel_1(X0,X5),X0,X0) & m1_subset_1(X5,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.87/0.99    inference(rectify,[],[f35])).
% 1.87/0.99  
% 1.87/0.99  fof(f43,plain,(
% 1.87/0.99    ! [X0] : (? [X5] : (~v5_pre_topc(k4_waybel_1(X0,X5),X0,X0) & m1_subset_1(X5,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0) & m1_subset_1(sK2(X0),u1_struct_0(X0))))),
% 1.87/0.99    introduced(choice_axiom,[])).
% 1.87/0.99  
% 1.87/0.99  fof(f44,plain,(
% 1.87/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | (~v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0) & m1_subset_1(sK2(X0),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.87/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).
% 1.87/0.99  
% 1.87/0.99  fof(f69,plain,(
% 1.87/0.99    ( ! [X4,X2,X0,X3,X1] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | ~v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f44])).
% 1.87/0.99  
% 1.87/0.99  fof(f92,plain,(
% 1.87/0.99    ( ! [X4,X0,X3,X1] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | ~v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.87/0.99    inference(equality_resolution,[],[f69])).
% 1.87/0.99  
% 1.87/0.99  fof(f84,plain,(
% 1.87/0.99    ( ! [X3] : (v5_pre_topc(k4_waybel_1(sK3,X3),sK3,sK3) | ~m1_subset_1(X3,u1_struct_0(sK3))) )),
% 1.87/0.99    inference(cnf_transformation,[],[f48])).
% 1.87/0.99  
% 1.87/0.99  fof(f70,plain,(
% 1.87/0.99    v2_pre_topc(sK3)),
% 1.87/0.99    inference(cnf_transformation,[],[f48])).
% 1.87/0.99  
% 1.87/0.99  fof(f71,plain,(
% 1.87/0.99    v8_pre_topc(sK3)),
% 1.87/0.99    inference(cnf_transformation,[],[f48])).
% 1.87/0.99  
% 1.87/0.99  fof(f72,plain,(
% 1.87/0.99    v3_orders_2(sK3)),
% 1.87/0.99    inference(cnf_transformation,[],[f48])).
% 1.87/0.99  
% 1.87/0.99  fof(f73,plain,(
% 1.87/0.99    v4_orders_2(sK3)),
% 1.87/0.99    inference(cnf_transformation,[],[f48])).
% 1.87/0.99  
% 1.87/0.99  fof(f75,plain,(
% 1.87/0.99    v1_lattice3(sK3)),
% 1.87/0.99    inference(cnf_transformation,[],[f48])).
% 1.87/0.99  
% 1.87/0.99  fof(f76,plain,(
% 1.87/0.99    v2_lattice3(sK3)),
% 1.87/0.99    inference(cnf_transformation,[],[f48])).
% 1.87/0.99  
% 1.87/0.99  fof(f77,plain,(
% 1.87/0.99    v1_compts_1(sK3)),
% 1.87/0.99    inference(cnf_transformation,[],[f48])).
% 1.87/0.99  
% 1.87/0.99  fof(f80,plain,(
% 1.87/0.99    ~v2_struct_0(sK5)),
% 1.87/0.99    inference(cnf_transformation,[],[f48])).
% 1.87/0.99  
% 1.87/0.99  fof(f81,plain,(
% 1.87/0.99    v4_orders_2(sK5)),
% 1.87/0.99    inference(cnf_transformation,[],[f48])).
% 1.87/0.99  
% 1.87/0.99  fof(f83,plain,(
% 1.87/0.99    l1_waybel_0(sK5,sK3)),
% 1.87/0.99    inference(cnf_transformation,[],[f48])).
% 1.87/0.99  
% 1.87/0.99  fof(f79,plain,(
% 1.87/0.99    m1_subset_1(sK4,u1_struct_0(sK3))),
% 1.87/0.99    inference(cnf_transformation,[],[f48])).
% 1.87/0.99  
% 1.87/0.99  fof(f68,plain,(
% 1.87/0.99    ( ! [X4,X2,X0,X3,X1] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | m1_subset_1(sK2(X0),u1_struct_0(X0)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f44])).
% 1.87/0.99  
% 1.87/0.99  fof(f93,plain,(
% 1.87/0.99    ( ! [X4,X0,X3,X1] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | m1_subset_1(sK2(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.87/0.99    inference(equality_resolution,[],[f68])).
% 1.87/0.99  
% 1.87/0.99  fof(f6,axiom,(
% 1.87/0.99    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 1.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f16,plain,(
% 1.87/0.99    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 1.87/0.99    inference(pure_predicate_removal,[],[f6])).
% 1.87/0.99  
% 1.87/0.99  fof(f17,plain,(
% 1.87/0.99    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))))),
% 1.87/0.99    inference(pure_predicate_removal,[],[f16])).
% 1.87/0.99  
% 1.87/0.99  fof(f25,plain,(
% 1.87/0.99    ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 1.87/0.99    inference(ennf_transformation,[],[f17])).
% 1.87/0.99  
% 1.87/0.99  fof(f26,plain,(
% 1.87/0.99    ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 1.87/0.99    inference(flattening,[],[f25])).
% 1.87/0.99  
% 1.87/0.99  fof(f61,plain,(
% 1.87/0.99    ( ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f26])).
% 1.87/0.99  
% 1.87/0.99  fof(f64,plain,(
% 1.87/0.99    ( ! [X0] : (l1_pre_topc(X0) | ~l1_waybel_9(X0)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f31])).
% 1.87/0.99  
% 1.87/0.99  fof(f3,axiom,(
% 1.87/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f20,plain,(
% 1.87/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.87/0.99    inference(ennf_transformation,[],[f3])).
% 1.87/0.99  
% 1.87/0.99  fof(f51,plain,(
% 1.87/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f20])).
% 1.87/0.99  
% 1.87/0.99  fof(f2,axiom,(
% 1.87/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f19,plain,(
% 1.87/0.99    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.87/0.99    inference(ennf_transformation,[],[f2])).
% 1.87/0.99  
% 1.87/0.99  fof(f50,plain,(
% 1.87/0.99    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.87/0.99    inference(cnf_transformation,[],[f19])).
% 1.87/0.99  
% 1.87/0.99  fof(f1,axiom,(
% 1.87/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f18,plain,(
% 1.87/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.87/0.99    inference(ennf_transformation,[],[f1])).
% 1.87/0.99  
% 1.87/0.99  fof(f49,plain,(
% 1.87/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.87/0.99    inference(cnf_transformation,[],[f18])).
% 1.87/0.99  
% 1.87/0.99  fof(f8,axiom,(
% 1.87/0.99    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (v1_relat_1(X1) => k2_yellow_0(X0,k2_relat_1(X1)) = k5_yellow_2(X0,X1)))),
% 1.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f29,plain,(
% 1.87/0.99    ! [X0] : (! [X1] : (k2_yellow_0(X0,k2_relat_1(X1)) = k5_yellow_2(X0,X1) | ~v1_relat_1(X1)) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 1.87/0.99    inference(ennf_transformation,[],[f8])).
% 1.87/0.99  
% 1.87/0.99  fof(f30,plain,(
% 1.87/0.99    ! [X0] : (! [X1] : (k2_yellow_0(X0,k2_relat_1(X1)) = k5_yellow_2(X0,X1) | ~v1_relat_1(X1)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 1.87/0.99    inference(flattening,[],[f29])).
% 1.87/0.99  
% 1.87/0.99  fof(f63,plain,(
% 1.87/0.99    ( ! [X0,X1] : (k2_yellow_0(X0,k2_relat_1(X1)) = k5_yellow_2(X0,X1) | ~v1_relat_1(X1) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f30])).
% 1.87/0.99  
% 1.87/0.99  fof(f4,axiom,(
% 1.87/0.99    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 1.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f21,plain,(
% 1.87/0.99    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 1.87/0.99    inference(ennf_transformation,[],[f4])).
% 1.87/0.99  
% 1.87/0.99  fof(f22,plain,(
% 1.87/0.99    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 1.87/0.99    inference(flattening,[],[f21])).
% 1.87/0.99  
% 1.87/0.99  fof(f52,plain,(
% 1.87/0.99    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f22])).
% 1.87/0.99  
% 1.87/0.99  fof(f7,axiom,(
% 1.87/0.99    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (l1_waybel_0(X1,X0) => k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1))))),
% 1.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f27,plain,(
% 1.87/0.99    ! [X0] : (! [X1] : (k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0)) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 1.87/0.99    inference(ennf_transformation,[],[f7])).
% 1.87/0.99  
% 1.87/0.99  fof(f28,plain,(
% 1.87/0.99    ! [X0] : (! [X1] : (k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 1.87/0.99    inference(flattening,[],[f27])).
% 1.87/0.99  
% 1.87/0.99  fof(f62,plain,(
% 1.87/0.99    ( ! [X0,X1] : (k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f28])).
% 1.87/0.99  
% 1.87/0.99  fof(f57,plain,(
% 1.87/0.99    ( ! [X2,X0,X1] : (k2_yellow_0(X0,X2) = X1 | ~r1_orders_2(X0,sK0(X0,X1,X2),X1) | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f39])).
% 1.87/0.99  
% 1.87/0.99  fof(f10,axiom,(
% 1.87/0.99    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & v11_waybel_0(X1,X0) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3))))))),
% 1.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f32,plain,(
% 1.87/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | (~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.87/0.99    inference(ennf_transformation,[],[f10])).
% 1.87/0.99  
% 1.87/0.99  fof(f33,plain,(
% 1.87/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.87/0.99    inference(flattening,[],[f32])).
% 1.87/0.99  
% 1.87/0.99  fof(f40,plain,(
% 1.87/0.99    ! [X0] : (? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0) & m1_subset_1(sK1(X0),u1_struct_0(X0))))),
% 1.87/0.99    introduced(choice_axiom,[])).
% 1.87/0.99  
% 1.87/0.99  fof(f41,plain,(
% 1.87/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | (~v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0) & m1_subset_1(sK1(X0),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.87/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f40])).
% 1.87/0.99  
% 1.87/0.99  fof(f67,plain,(
% 1.87/0.99    ( ! [X2,X0,X3,X1] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f41])).
% 1.87/0.99  
% 1.87/0.99  fof(f90,plain,(
% 1.87/0.99    ( ! [X0,X3,X1] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v11_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.87/0.99    inference(equality_resolution,[],[f67])).
% 1.87/0.99  
% 1.87/0.99  fof(f85,plain,(
% 1.87/0.99    v11_waybel_0(sK5,sK3)),
% 1.87/0.99    inference(cnf_transformation,[],[f48])).
% 1.87/0.99  
% 1.87/0.99  fof(f66,plain,(
% 1.87/0.99    ( ! [X2,X0,X3,X1] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | m1_subset_1(sK1(X0),u1_struct_0(X0)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f41])).
% 1.87/0.99  
% 1.87/0.99  fof(f91,plain,(
% 1.87/0.99    ( ! [X0,X3,X1] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v11_waybel_0(X1,X0) | m1_subset_1(sK1(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.87/0.99    inference(equality_resolution,[],[f66])).
% 1.87/0.99  
% 1.87/0.99  fof(f87,plain,(
% 1.87/0.99    k1_waybel_9(sK3,sK5) != sK4),
% 1.87/0.99    inference(cnf_transformation,[],[f48])).
% 1.87/0.99  
% 1.87/0.99  cnf(c_9,plain,
% 1.87/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 1.87/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.87/0.99      | m1_subset_1(sK0(X0,X2,X1),u1_struct_0(X0))
% 1.87/0.99      | ~ v5_orders_2(X0)
% 1.87/0.99      | ~ l1_orders_2(X0)
% 1.87/0.99      | k2_yellow_0(X0,X1) = X2 ),
% 1.87/0.99      inference(cnf_transformation,[],[f55]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_34,negated_conjecture,
% 1.87/0.99      ( v5_orders_2(sK3) ),
% 1.87/0.99      inference(cnf_transformation,[],[f74]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1019,plain,
% 1.87/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 1.87/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.87/0.99      | m1_subset_1(sK0(X0,X2,X1),u1_struct_0(X0))
% 1.87/0.99      | ~ l1_orders_2(X0)
% 1.87/0.99      | k2_yellow_0(X0,X1) = X2
% 1.87/0.99      | sK3 != X0 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_34]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1020,plain,
% 1.87/0.99      ( ~ r1_lattice3(sK3,X0,X1)
% 1.87/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/0.99      | m1_subset_1(sK0(sK3,X1,X0),u1_struct_0(sK3))
% 1.87/0.99      | ~ l1_orders_2(sK3)
% 1.87/0.99      | k2_yellow_0(sK3,X0) = X1 ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_1019]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_30,negated_conjecture,
% 1.87/0.99      ( l1_waybel_9(sK3) ),
% 1.87/0.99      inference(cnf_transformation,[],[f78]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_15,plain,
% 1.87/0.99      ( ~ l1_waybel_9(X0) | l1_orders_2(X0) ),
% 1.87/0.99      inference(cnf_transformation,[],[f65]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_74,plain,
% 1.87/0.99      ( ~ l1_waybel_9(sK3) | l1_orders_2(sK3) ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1024,plain,
% 1.87/0.99      ( m1_subset_1(sK0(sK3,X1,X0),u1_struct_0(sK3))
% 1.87/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/0.99      | ~ r1_lattice3(sK3,X0,X1)
% 1.87/0.99      | k2_yellow_0(sK3,X0) = X1 ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_1020,c_30,c_74]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1025,plain,
% 1.87/0.99      ( ~ r1_lattice3(sK3,X0,X1)
% 1.87/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/0.99      | m1_subset_1(sK0(sK3,X1,X0),u1_struct_0(sK3))
% 1.87/0.99      | k2_yellow_0(sK3,X0) = X1 ),
% 1.87/0.99      inference(renaming,[status(thm)],[c_1024]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2118,plain,
% 1.87/0.99      ( ~ r1_lattice3(sK3,X0_69,X0_67)
% 1.87/0.99      | ~ m1_subset_1(X0_67,u1_struct_0(sK3))
% 1.87/0.99      | m1_subset_1(sK0(sK3,X0_67,X0_69),u1_struct_0(sK3))
% 1.87/0.99      | k2_yellow_0(sK3,X0_69) = X0_67 ),
% 1.87/0.99      inference(subtyping,[status(esa)],[c_1025]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2572,plain,
% 1.87/0.99      ( k2_yellow_0(sK3,X0_69) = X0_67
% 1.87/0.99      | r1_lattice3(sK3,X0_69,X0_67) != iProver_top
% 1.87/0.99      | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top
% 1.87/0.99      | m1_subset_1(sK0(sK3,X0_67,X0_69),u1_struct_0(sK3)) = iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_2118]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_8,plain,
% 1.87/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 1.87/0.99      | r1_lattice3(X0,X1,sK0(X0,X2,X1))
% 1.87/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.87/0.99      | ~ v5_orders_2(X0)
% 1.87/0.99      | ~ l1_orders_2(X0)
% 1.87/0.99      | k2_yellow_0(X0,X1) = X2 ),
% 1.87/0.99      inference(cnf_transformation,[],[f56]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1043,plain,
% 1.87/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 1.87/0.99      | r1_lattice3(X0,X1,sK0(X0,X2,X1))
% 1.87/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.87/0.99      | ~ l1_orders_2(X0)
% 1.87/0.99      | k2_yellow_0(X0,X1) = X2
% 1.87/0.99      | sK3 != X0 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_34]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1044,plain,
% 1.87/0.99      ( ~ r1_lattice3(sK3,X0,X1)
% 1.87/0.99      | r1_lattice3(sK3,X0,sK0(sK3,X1,X0))
% 1.87/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/0.99      | ~ l1_orders_2(sK3)
% 1.87/0.99      | k2_yellow_0(sK3,X0) = X1 ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_1043]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1048,plain,
% 1.87/0.99      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/0.99      | r1_lattice3(sK3,X0,sK0(sK3,X1,X0))
% 1.87/0.99      | ~ r1_lattice3(sK3,X0,X1)
% 1.87/0.99      | k2_yellow_0(sK3,X0) = X1 ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_1044,c_30,c_74]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1049,plain,
% 1.87/0.99      ( ~ r1_lattice3(sK3,X0,X1)
% 1.87/0.99      | r1_lattice3(sK3,X0,sK0(sK3,X1,X0))
% 1.87/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/0.99      | k2_yellow_0(sK3,X0) = X1 ),
% 1.87/0.99      inference(renaming,[status(thm)],[c_1048]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2117,plain,
% 1.87/0.99      ( ~ r1_lattice3(sK3,X0_69,X0_67)
% 1.87/0.99      | r1_lattice3(sK3,X0_69,sK0(sK3,X0_67,X0_69))
% 1.87/0.99      | ~ m1_subset_1(X0_67,u1_struct_0(sK3))
% 1.87/0.99      | k2_yellow_0(sK3,X0_69) = X0_67 ),
% 1.87/0.99      inference(subtyping,[status(esa)],[c_1049]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2573,plain,
% 1.87/0.99      ( k2_yellow_0(sK3,X0_69) = X0_67
% 1.87/0.99      | r1_lattice3(sK3,X0_69,X0_67) != iProver_top
% 1.87/0.99      | r1_lattice3(sK3,X0_69,sK0(sK3,X0_67,X0_69)) = iProver_top
% 1.87/0.99      | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_2117]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_22,negated_conjecture,
% 1.87/0.99      ( r3_waybel_9(sK3,sK5,sK4) ),
% 1.87/0.99      inference(cnf_transformation,[],[f86]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_26,negated_conjecture,
% 1.87/0.99      ( v7_waybel_0(sK5) ),
% 1.87/0.99      inference(cnf_transformation,[],[f82]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_19,plain,
% 1.87/0.99      ( ~ v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0)
% 1.87/0.99      | ~ r3_waybel_9(X0,X1,X2)
% 1.87/0.99      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 1.87/0.99      | r1_orders_2(X0,X3,X2)
% 1.87/0.99      | ~ l1_waybel_0(X1,X0)
% 1.87/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.87/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.87/0.99      | ~ v2_pre_topc(X0)
% 1.87/0.99      | ~ v8_pre_topc(X0)
% 1.87/0.99      | ~ v3_orders_2(X0)
% 1.87/0.99      | ~ v2_lattice3(X0)
% 1.87/0.99      | ~ v1_compts_1(X0)
% 1.87/0.99      | ~ v4_orders_2(X1)
% 1.87/0.99      | ~ v4_orders_2(X0)
% 1.87/0.99      | ~ v7_waybel_0(X1)
% 1.87/0.99      | ~ l1_waybel_9(X0)
% 1.87/0.99      | ~ v5_orders_2(X0)
% 1.87/0.99      | ~ v1_lattice3(X0)
% 1.87/0.99      | v2_struct_0(X1) ),
% 1.87/0.99      inference(cnf_transformation,[],[f92]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_24,negated_conjecture,
% 1.87/0.99      ( v5_pre_topc(k4_waybel_1(sK3,X0),sK3,sK3)
% 1.87/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 1.87/0.99      inference(cnf_transformation,[],[f84]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_535,plain,
% 1.87/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 1.87/0.99      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 1.87/0.99      | r1_orders_2(X0,X3,X2)
% 1.87/0.99      | ~ l1_waybel_0(X1,X0)
% 1.87/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.87/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.87/0.99      | ~ m1_subset_1(X4,u1_struct_0(sK3))
% 1.87/0.99      | ~ v2_pre_topc(X0)
% 1.87/0.99      | ~ v8_pre_topc(X0)
% 1.87/0.99      | ~ v3_orders_2(X0)
% 1.87/0.99      | ~ v2_lattice3(X0)
% 1.87/0.99      | ~ v1_compts_1(X0)
% 1.87/0.99      | ~ v4_orders_2(X1)
% 1.87/0.99      | ~ v4_orders_2(X0)
% 1.87/0.99      | ~ v7_waybel_0(X1)
% 1.87/0.99      | ~ l1_waybel_9(X0)
% 1.87/0.99      | ~ v5_orders_2(X0)
% 1.87/0.99      | ~ v1_lattice3(X0)
% 1.87/0.99      | v2_struct_0(X1)
% 1.87/0.99      | k4_waybel_1(X0,sK2(X0)) != k4_waybel_1(sK3,X4)
% 1.87/0.99      | sK3 != X0 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_24]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_536,plain,
% 1.87/0.99      ( ~ r3_waybel_9(sK3,X0,X1)
% 1.87/0.99      | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
% 1.87/0.99      | r1_orders_2(sK3,X2,X1)
% 1.87/0.99      | ~ l1_waybel_0(X0,sK3)
% 1.87/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 1.87/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.87/0.99      | ~ v2_pre_topc(sK3)
% 1.87/0.99      | ~ v8_pre_topc(sK3)
% 1.87/0.99      | ~ v3_orders_2(sK3)
% 1.87/0.99      | ~ v2_lattice3(sK3)
% 1.87/0.99      | ~ v1_compts_1(sK3)
% 1.87/0.99      | ~ v4_orders_2(X0)
% 1.87/0.99      | ~ v4_orders_2(sK3)
% 1.87/0.99      | ~ v7_waybel_0(X0)
% 1.87/0.99      | ~ l1_waybel_9(sK3)
% 1.87/0.99      | ~ v5_orders_2(sK3)
% 1.87/0.99      | ~ v1_lattice3(sK3)
% 1.87/0.99      | v2_struct_0(X0)
% 1.87/0.99      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X3) ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_535]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_38,negated_conjecture,
% 1.87/0.99      ( v2_pre_topc(sK3) ),
% 1.87/0.99      inference(cnf_transformation,[],[f70]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_37,negated_conjecture,
% 1.87/0.99      ( v8_pre_topc(sK3) ),
% 1.87/0.99      inference(cnf_transformation,[],[f71]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_36,negated_conjecture,
% 1.87/0.99      ( v3_orders_2(sK3) ),
% 1.87/0.99      inference(cnf_transformation,[],[f72]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_35,negated_conjecture,
% 1.87/0.99      ( v4_orders_2(sK3) ),
% 1.87/0.99      inference(cnf_transformation,[],[f73]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_33,negated_conjecture,
% 1.87/0.99      ( v1_lattice3(sK3) ),
% 1.87/0.99      inference(cnf_transformation,[],[f75]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_32,negated_conjecture,
% 1.87/0.99      ( v2_lattice3(sK3) ),
% 1.87/0.99      inference(cnf_transformation,[],[f76]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_31,negated_conjecture,
% 1.87/0.99      ( v1_compts_1(sK3) ),
% 1.87/0.99      inference(cnf_transformation,[],[f77]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_540,plain,
% 1.87/0.99      ( ~ v7_waybel_0(X0)
% 1.87/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.87/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 1.87/0.99      | ~ l1_waybel_0(X0,sK3)
% 1.87/0.99      | r1_orders_2(sK3,X2,X1)
% 1.87/0.99      | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
% 1.87/0.99      | ~ r3_waybel_9(sK3,X0,X1)
% 1.87/0.99      | ~ v4_orders_2(X0)
% 1.87/0.99      | v2_struct_0(X0)
% 1.87/0.99      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X3) ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_536,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_31,c_30]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_541,plain,
% 1.87/0.99      ( ~ r3_waybel_9(sK3,X0,X1)
% 1.87/0.99      | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
% 1.87/0.99      | r1_orders_2(sK3,X2,X1)
% 1.87/0.99      | ~ l1_waybel_0(X0,sK3)
% 1.87/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.87/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 1.87/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/0.99      | ~ v4_orders_2(X0)
% 1.87/0.99      | ~ v7_waybel_0(X0)
% 1.87/0.99      | v2_struct_0(X0)
% 1.87/0.99      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X3) ),
% 1.87/0.99      inference(renaming,[status(thm)],[c_540]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_731,plain,
% 1.87/0.99      ( ~ r3_waybel_9(sK3,X0,X1)
% 1.87/0.99      | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
% 1.87/0.99      | r1_orders_2(sK3,X2,X1)
% 1.87/0.99      | ~ l1_waybel_0(X0,sK3)
% 1.87/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.87/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 1.87/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/0.99      | ~ v4_orders_2(X0)
% 1.87/0.99      | v2_struct_0(X0)
% 1.87/0.99      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X3)
% 1.87/0.99      | sK5 != X0 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_541]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_732,plain,
% 1.87/0.99      ( ~ r3_waybel_9(sK3,sK5,X0)
% 1.87/0.99      | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
% 1.87/0.99      | r1_orders_2(sK3,X1,X0)
% 1.87/0.99      | ~ l1_waybel_0(sK5,sK3)
% 1.87/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.87/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/0.99      | ~ v4_orders_2(sK5)
% 1.87/0.99      | v2_struct_0(sK5)
% 1.87/0.99      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X2) ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_731]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_28,negated_conjecture,
% 1.87/0.99      ( ~ v2_struct_0(sK5) ),
% 1.87/0.99      inference(cnf_transformation,[],[f80]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_27,negated_conjecture,
% 1.87/0.99      ( v4_orders_2(sK5) ),
% 1.87/0.99      inference(cnf_transformation,[],[f81]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_25,negated_conjecture,
% 1.87/0.99      ( l1_waybel_0(sK5,sK3) ),
% 1.87/0.99      inference(cnf_transformation,[],[f83]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_736,plain,
% 1.87/0.99      ( r1_orders_2(sK3,X1,X0)
% 1.87/0.99      | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
% 1.87/0.99      | ~ r3_waybel_9(sK3,sK5,X0)
% 1.87/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.87/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/0.99      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X2) ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_732,c_28,c_27,c_25]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_737,plain,
% 1.87/0.99      ( ~ r3_waybel_9(sK3,sK5,X0)
% 1.87/0.99      | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
% 1.87/0.99      | r1_orders_2(sK3,X1,X0)
% 1.87/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.87/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/0.99      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X2) ),
% 1.87/0.99      inference(renaming,[status(thm)],[c_736]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_867,plain,
% 1.87/0.99      ( ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.87/0.99      | r1_orders_2(sK3,X0,X1)
% 1.87/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.87/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/0.99      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X2)
% 1.87/0.99      | sK4 != X1
% 1.87/0.99      | sK5 != sK5
% 1.87/0.99      | sK3 != sK3 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_737]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_868,plain,
% 1.87/0.99      ( ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.87/0.99      | r1_orders_2(sK3,X0,sK4)
% 1.87/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/0.99      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 1.87/0.99      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1) ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_867]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_29,negated_conjecture,
% 1.87/0.99      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 1.87/0.99      inference(cnf_transformation,[],[f79]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_872,plain,
% 1.87/0.99      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/0.99      | r1_orders_2(sK3,X0,sK4)
% 1.87/0.99      | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.87/0.99      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1) ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_868,c_29]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_873,plain,
% 1.87/0.99      ( ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.87/0.99      | r1_orders_2(sK3,X0,sK4)
% 1.87/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/0.99      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1) ),
% 1.87/0.99      inference(renaming,[status(thm)],[c_872]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2124,plain,
% 1.87/0.99      ( ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_67)
% 1.87/0.99      | r1_orders_2(sK3,X0_67,sK4)
% 1.87/0.99      | ~ m1_subset_1(X1_67,u1_struct_0(sK3))
% 1.87/0.99      | ~ m1_subset_1(X0_67,u1_struct_0(sK3))
% 1.87/0.99      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X1_67) ),
% 1.87/0.99      inference(subtyping,[status(esa)],[c_873]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2133,plain,
% 1.87/0.99      ( ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_67)
% 1.87/0.99      | r1_orders_2(sK3,X0_67,sK4)
% 1.87/0.99      | ~ m1_subset_1(X0_67,u1_struct_0(sK3))
% 1.87/0.99      | ~ sP1_iProver_split ),
% 1.87/0.99      inference(splitting,
% 1.87/0.99                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 1.87/0.99                [c_2124]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2565,plain,
% 1.87/0.99      ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_67) != iProver_top
% 1.87/0.99      | r1_orders_2(sK3,X0_67,sK4) = iProver_top
% 1.87/0.99      | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top
% 1.87/0.99      | sP1_iProver_split != iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_2133]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2134,plain,
% 1.87/0.99      ( sP1_iProver_split | sP0_iProver_split ),
% 1.87/0.99      inference(splitting,
% 1.87/0.99                [splitting(split),new_symbols(definition,[])],
% 1.87/0.99                [c_2124]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2196,plain,
% 1.87/0.99      ( sP1_iProver_split = iProver_top
% 1.87/0.99      | sP0_iProver_split = iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_2134]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2197,plain,
% 1.87/0.99      ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_67) != iProver_top
% 1.87/0.99      | r1_orders_2(sK3,X0_67,sK4) = iProver_top
% 1.87/0.99      | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top
% 1.87/0.99      | sP1_iProver_split != iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_2133]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_20,plain,
% 1.87/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 1.87/0.99      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 1.87/0.99      | r1_orders_2(X0,X3,X2)
% 1.87/0.99      | ~ l1_waybel_0(X1,X0)
% 1.87/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.87/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.87/0.99      | m1_subset_1(sK2(X0),u1_struct_0(X0))
% 1.87/0.99      | ~ v2_pre_topc(X0)
% 1.87/0.99      | ~ v8_pre_topc(X0)
% 1.87/0.99      | ~ v3_orders_2(X0)
% 1.87/0.99      | ~ v2_lattice3(X0)
% 1.87/0.99      | ~ v1_compts_1(X0)
% 1.87/0.99      | ~ v4_orders_2(X1)
% 1.87/0.99      | ~ v4_orders_2(X0)
% 1.87/0.99      | ~ v7_waybel_0(X1)
% 1.87/0.99      | ~ l1_waybel_9(X0)
% 1.87/0.99      | ~ v5_orders_2(X0)
% 1.87/0.99      | ~ v1_lattice3(X0)
% 1.87/0.99      | v2_struct_0(X1) ),
% 1.87/0.99      inference(cnf_transformation,[],[f93]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_611,plain,
% 1.87/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 1.87/0.99      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 1.87/0.99      | r1_orders_2(X0,X3,X2)
% 1.87/0.99      | ~ l1_waybel_0(X1,X0)
% 1.87/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.87/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.87/0.99      | m1_subset_1(sK2(X0),u1_struct_0(X0))
% 1.87/0.99      | ~ v2_pre_topc(X0)
% 1.87/0.99      | ~ v8_pre_topc(X0)
% 1.87/0.99      | ~ v3_orders_2(X0)
% 1.87/0.99      | ~ v2_lattice3(X0)
% 1.87/0.99      | ~ v4_orders_2(X1)
% 1.87/0.99      | ~ v4_orders_2(X0)
% 1.87/0.99      | ~ v7_waybel_0(X1)
% 1.87/0.99      | ~ l1_waybel_9(X0)
% 1.87/0.99      | ~ v5_orders_2(X0)
% 1.87/0.99      | ~ v1_lattice3(X0)
% 1.87/0.99      | v2_struct_0(X1)
% 1.87/0.99      | sK3 != X0 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_31]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_612,plain,
% 1.87/0.99      ( ~ r3_waybel_9(sK3,X0,X1)
% 1.87/0.99      | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
% 1.87/0.99      | r1_orders_2(sK3,X2,X1)
% 1.87/0.99      | ~ l1_waybel_0(X0,sK3)
% 1.87/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.87/0.99      | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
% 1.87/0.99      | ~ v2_pre_topc(sK3)
% 1.87/0.99      | ~ v8_pre_topc(sK3)
% 1.87/0.99      | ~ v3_orders_2(sK3)
% 1.87/0.99      | ~ v2_lattice3(sK3)
% 1.87/0.99      | ~ v4_orders_2(X0)
% 1.87/0.99      | ~ v4_orders_2(sK3)
% 1.87/0.99      | ~ v7_waybel_0(X0)
% 1.87/0.99      | ~ l1_waybel_9(sK3)
% 1.87/0.99      | ~ v5_orders_2(sK3)
% 1.87/0.99      | ~ v1_lattice3(sK3)
% 1.87/0.99      | v2_struct_0(X0) ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_611]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_616,plain,
% 1.87/0.99      ( ~ v7_waybel_0(X0)
% 1.87/0.99      | ~ r3_waybel_9(sK3,X0,X1)
% 1.87/0.99      | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
% 1.87/0.99      | r1_orders_2(sK3,X2,X1)
% 1.87/0.99      | ~ l1_waybel_0(X0,sK3)
% 1.87/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.87/0.99      | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
% 1.87/0.99      | ~ v4_orders_2(X0)
% 1.87/0.99      | v2_struct_0(X0) ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_612,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_30]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_617,plain,
% 1.87/0.99      ( ~ r3_waybel_9(sK3,X0,X1)
% 1.87/0.99      | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
% 1.87/0.99      | r1_orders_2(sK3,X2,X1)
% 1.87/0.99      | ~ l1_waybel_0(X0,sK3)
% 1.87/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.87/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/0.99      | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
% 1.87/0.99      | ~ v4_orders_2(X0)
% 1.87/0.99      | ~ v7_waybel_0(X0)
% 1.87/0.99      | v2_struct_0(X0) ),
% 1.87/0.99      inference(renaming,[status(thm)],[c_616]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_701,plain,
% 1.87/0.99      ( ~ r3_waybel_9(sK3,X0,X1)
% 1.87/0.99      | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),u1_waybel_0(sK3,X0)),X2)
% 1.87/0.99      | r1_orders_2(sK3,X2,X1)
% 1.87/0.99      | ~ l1_waybel_0(X0,sK3)
% 1.87/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.87/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/0.99      | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
% 1.87/0.99      | ~ v4_orders_2(X0)
% 1.87/0.99      | v2_struct_0(X0)
% 1.87/0.99      | sK5 != X0 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_617]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_702,plain,
% 1.87/0.99      ( ~ r3_waybel_9(sK3,sK5,X0)
% 1.87/0.99      | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
% 1.87/0.99      | r1_orders_2(sK3,X1,X0)
% 1.87/0.99      | ~ l1_waybel_0(sK5,sK3)
% 1.87/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/0.99      | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
% 1.87/0.99      | ~ v4_orders_2(sK5)
% 1.87/0.99      | v2_struct_0(sK5) ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_701]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_706,plain,
% 1.87/0.99      ( r1_orders_2(sK3,X1,X0)
% 1.87/0.99      | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
% 1.87/0.99      | ~ r3_waybel_9(sK3,sK5,X0)
% 1.87/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/0.99      | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_702,c_28,c_27,c_25]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_707,plain,
% 1.87/0.99      ( ~ r3_waybel_9(sK3,sK5,X0)
% 1.87/0.99      | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X1)
% 1.87/0.99      | r1_orders_2(sK3,X1,X0)
% 1.87/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/0.99      | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) ),
% 1.87/0.99      inference(renaming,[status(thm)],[c_706]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_894,plain,
% 1.87/0.99      ( ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.87/0.99      | r1_orders_2(sK3,X0,X1)
% 1.87/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/0.99      | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
% 1.87/0.99      | sK4 != X1
% 1.87/0.99      | sK5 != sK5
% 1.87/0.99      | sK3 != sK3 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_707]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_895,plain,
% 1.87/0.99      ( ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.87/0.99      | r1_orders_2(sK3,X0,sK4)
% 1.87/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/0.99      | m1_subset_1(sK2(sK3),u1_struct_0(sK3))
% 1.87/0.99      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_894]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_899,plain,
% 1.87/0.99      ( m1_subset_1(sK2(sK3),u1_struct_0(sK3))
% 1.87/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/0.99      | r1_orders_2(sK3,X0,sK4)
% 1.87/0.99      | ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0) ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_895,c_29]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_900,plain,
% 1.87/0.99      ( ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.87/0.99      | r1_orders_2(sK3,X0,sK4)
% 1.87/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/0.99      | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) ),
% 1.87/0.99      inference(renaming,[status(thm)],[c_899]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2123,plain,
% 1.87/0.99      ( ~ r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_67)
% 1.87/0.99      | r1_orders_2(sK3,X0_67,sK4)
% 1.87/0.99      | ~ m1_subset_1(X0_67,u1_struct_0(sK3))
% 1.87/0.99      | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) ),
% 1.87/0.99      inference(subtyping,[status(esa)],[c_900]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2203,plain,
% 1.87/0.99      ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_67) != iProver_top
% 1.87/0.99      | r1_orders_2(sK3,X0_67,sK4) = iProver_top
% 1.87/0.99      | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top
% 1.87/0.99      | m1_subset_1(sK2(sK3),u1_struct_0(sK3)) = iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_2123]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2132,plain,
% 1.87/0.99      ( ~ m1_subset_1(X0_67,u1_struct_0(sK3))
% 1.87/0.99      | k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X0_67)
% 1.87/0.99      | ~ sP0_iProver_split ),
% 1.87/0.99      inference(splitting,
% 1.87/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.87/0.99                [c_2124]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2566,plain,
% 1.87/0.99      ( k4_waybel_1(sK3,sK2(sK3)) != k4_waybel_1(sK3,X0_67)
% 1.87/0.99      | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top
% 1.87/0.99      | sP0_iProver_split != iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_2132]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2766,plain,
% 1.87/0.99      ( m1_subset_1(sK2(sK3),u1_struct_0(sK3)) != iProver_top
% 1.87/0.99      | sP0_iProver_split != iProver_top ),
% 1.87/0.99      inference(equality_resolution,[status(thm)],[c_2566]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2980,plain,
% 1.87/0.99      ( m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top
% 1.87/0.99      | r1_orders_2(sK3,X0_67,sK4) = iProver_top
% 1.87/0.99      | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_67) != iProver_top ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_2565,c_2196,c_2197,c_2203,c_2766]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2981,plain,
% 1.87/0.99      ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0_67) != iProver_top
% 1.87/0.99      | r1_orders_2(sK3,X0_67,sK4) = iProver_top
% 1.87/0.99      | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top ),
% 1.87/0.99      inference(renaming,[status(thm)],[c_2980]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_12,plain,
% 1.87/0.99      ( ~ l1_waybel_0(X0,X1)
% 1.87/0.99      | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.87/0.99      | ~ l1_struct_0(X1) ),
% 1.87/0.99      inference(cnf_transformation,[],[f61]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_16,plain,
% 1.87/0.99      ( ~ l1_waybel_9(X0) | l1_pre_topc(X0) ),
% 1.87/0.99      inference(cnf_transformation,[],[f64]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2,plain,
% 1.87/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.87/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_422,plain,
% 1.87/0.99      ( ~ l1_waybel_9(X0) | l1_struct_0(X0) ),
% 1.87/0.99      inference(resolution,[status(thm)],[c_16,c_2]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_436,plain,
% 1.87/0.99      ( ~ l1_waybel_0(X0,X1)
% 1.87/0.99      | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.87/0.99      | ~ l1_waybel_9(X2)
% 1.87/0.99      | X2 != X1 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_422]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_437,plain,
% 1.87/0.99      ( ~ l1_waybel_0(X0,X1)
% 1.87/0.99      | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.87/0.99      | ~ l1_waybel_9(X1) ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_436]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_677,plain,
% 1.87/0.99      ( ~ l1_waybel_0(X0,X1)
% 1.87/0.99      | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.87/0.99      | sK3 != X1 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_437,c_30]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_678,plain,
% 1.87/0.99      ( ~ l1_waybel_0(X0,sK3)
% 1.87/0.99      | m1_subset_1(u1_waybel_0(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_677]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_787,plain,
% 1.87/0.99      ( m1_subset_1(u1_waybel_0(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
% 1.87/0.99      | sK5 != X0
% 1.87/0.99      | sK3 != sK3 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_678]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_788,plain,
% 1.87/0.99      ( m1_subset_1(u1_waybel_0(sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_787]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2126,plain,
% 1.87/0.99      ( m1_subset_1(u1_waybel_0(sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 1.87/0.99      inference(subtyping,[status(esa)],[c_788]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2562,plain,
% 1.87/0.99      ( m1_subset_1(u1_waybel_0(sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_2126]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1,plain,
% 1.87/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.87/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 1.87/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2130,plain,
% 1.87/0.99      ( ~ m1_subset_1(X0_67,k1_zfmisc_1(k2_zfmisc_1(X0_70,X1_70)))
% 1.87/0.99      | k2_relset_1(X0_70,X1_70,X0_67) = k2_relat_1(X0_67) ),
% 1.87/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2560,plain,
% 1.87/0.99      ( k2_relset_1(X0_70,X1_70,X0_67) = k2_relat_1(X0_67)
% 1.87/0.99      | m1_subset_1(X0_67,k1_zfmisc_1(k2_zfmisc_1(X0_70,X1_70))) != iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_2130]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2822,plain,
% 1.87/0.99      ( k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)) = k2_relat_1(u1_waybel_0(sK3,sK5)) ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_2562,c_2560]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2986,plain,
% 1.87/0.99      ( r1_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_67) != iProver_top
% 1.87/0.99      | r1_orders_2(sK3,X0_67,sK4) = iProver_top
% 1.87/0.99      | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top ),
% 1.87/0.99      inference(light_normalisation,[status(thm)],[c_2981,c_2822]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3096,plain,
% 1.87/0.99      ( k2_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = X0_67
% 1.87/0.99      | r1_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_67) != iProver_top
% 1.87/0.99      | r1_orders_2(sK3,sK0(sK3,X0_67,k2_relat_1(u1_waybel_0(sK3,sK5))),sK4) = iProver_top
% 1.87/0.99      | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top
% 1.87/0.99      | m1_subset_1(sK0(sK3,X0_67,k2_relat_1(u1_waybel_0(sK3,sK5))),u1_struct_0(sK3)) != iProver_top ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_2573,c_2986]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_0,plain,
% 1.87/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.87/0.99      | v1_relat_1(X0) ),
% 1.87/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2131,plain,
% 1.87/0.99      ( ~ m1_subset_1(X0_67,k1_zfmisc_1(k2_zfmisc_1(X0_70,X1_70)))
% 1.87/0.99      | v1_relat_1(X0_67) ),
% 1.87/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2559,plain,
% 1.87/0.99      ( m1_subset_1(X0_67,k1_zfmisc_1(k2_zfmisc_1(X0_70,X1_70))) != iProver_top
% 1.87/0.99      | v1_relat_1(X0_67) = iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_2131]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2817,plain,
% 1.87/0.99      ( v1_relat_1(u1_waybel_0(sK3,sK5)) = iProver_top ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_2562,c_2559]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_14,plain,
% 1.87/0.99      ( ~ l1_orders_2(X0)
% 1.87/0.99      | v2_struct_0(X0)
% 1.87/0.99      | ~ v1_relat_1(X1)
% 1.87/0.99      | k2_yellow_0(X0,k2_relat_1(X1)) = k5_yellow_2(X0,X1) ),
% 1.87/0.99      inference(cnf_transformation,[],[f63]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3,plain,
% 1.87/0.99      ( ~ l1_orders_2(X0) | ~ v1_lattice3(X0) | ~ v2_struct_0(X0) ),
% 1.87/0.99      inference(cnf_transformation,[],[f52]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_664,plain,
% 1.87/0.99      ( ~ l1_orders_2(X0) | ~ v2_struct_0(X0) | sK3 != X0 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_33]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_665,plain,
% 1.87/0.99      ( ~ l1_orders_2(sK3) | ~ v2_struct_0(sK3) ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_664]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_110,plain,
% 1.87/0.99      ( ~ l1_orders_2(sK3) | ~ v1_lattice3(sK3) | ~ v2_struct_0(sK3) ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_667,plain,
% 1.87/0.99      ( ~ v2_struct_0(sK3) ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_665,c_33,c_30,c_74,c_110]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_812,plain,
% 1.87/0.99      ( ~ l1_orders_2(X0)
% 1.87/0.99      | ~ v1_relat_1(X1)
% 1.87/0.99      | k2_yellow_0(X0,k2_relat_1(X1)) = k5_yellow_2(X0,X1)
% 1.87/0.99      | sK3 != X0 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_667]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_813,plain,
% 1.87/0.99      ( ~ l1_orders_2(sK3)
% 1.87/0.99      | ~ v1_relat_1(X0)
% 1.87/0.99      | k2_yellow_0(sK3,k2_relat_1(X0)) = k5_yellow_2(sK3,X0) ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_812]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_817,plain,
% 1.87/0.99      ( ~ v1_relat_1(X0)
% 1.87/0.99      | k2_yellow_0(sK3,k2_relat_1(X0)) = k5_yellow_2(sK3,X0) ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_813,c_30,c_74]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2125,plain,
% 1.87/0.99      ( ~ v1_relat_1(X0_67)
% 1.87/0.99      | k2_yellow_0(sK3,k2_relat_1(X0_67)) = k5_yellow_2(sK3,X0_67) ),
% 1.87/0.99      inference(subtyping,[status(esa)],[c_817]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2563,plain,
% 1.87/0.99      ( k2_yellow_0(sK3,k2_relat_1(X0_67)) = k5_yellow_2(sK3,X0_67)
% 1.87/0.99      | v1_relat_1(X0_67) != iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_2125]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3145,plain,
% 1.87/0.99      ( k2_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = k5_yellow_2(sK3,u1_waybel_0(sK3,sK5)) ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_2817,c_2563]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_13,plain,
% 1.87/0.99      ( ~ l1_waybel_0(X0,X1)
% 1.87/0.99      | ~ l1_orders_2(X1)
% 1.87/0.99      | v2_struct_0(X1)
% 1.87/0.99      | k5_yellow_2(X1,u1_waybel_0(X1,X0)) = k1_waybel_9(X1,X0) ),
% 1.87/0.99      inference(cnf_transformation,[],[f62]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_779,plain,
% 1.87/0.99      ( ~ l1_orders_2(X0)
% 1.87/0.99      | v2_struct_0(X0)
% 1.87/0.99      | k5_yellow_2(X0,u1_waybel_0(X0,X1)) = k1_waybel_9(X0,X1)
% 1.87/0.99      | sK5 != X1
% 1.87/0.99      | sK3 != X0 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_25]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_780,plain,
% 1.87/0.99      ( ~ l1_orders_2(sK3)
% 1.87/0.99      | v2_struct_0(sK3)
% 1.87/0.99      | k5_yellow_2(sK3,u1_waybel_0(sK3,sK5)) = k1_waybel_9(sK3,sK5) ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_779]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_782,plain,
% 1.87/0.99      ( k5_yellow_2(sK3,u1_waybel_0(sK3,sK5)) = k1_waybel_9(sK3,sK5) ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_780,c_33,c_30,c_74,c_110]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2127,plain,
% 1.87/0.99      ( k5_yellow_2(sK3,u1_waybel_0(sK3,sK5)) = k1_waybel_9(sK3,sK5) ),
% 1.87/0.99      inference(subtyping,[status(esa)],[c_782]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3146,plain,
% 1.87/0.99      ( k2_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = k1_waybel_9(sK3,sK5) ),
% 1.87/0.99      inference(light_normalisation,[status(thm)],[c_3145,c_2127]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3289,plain,
% 1.87/0.99      ( k1_waybel_9(sK3,sK5) = X0_67
% 1.87/0.99      | r1_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_67) != iProver_top
% 1.87/0.99      | r1_orders_2(sK3,sK0(sK3,X0_67,k2_relat_1(u1_waybel_0(sK3,sK5))),sK4) = iProver_top
% 1.87/0.99      | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top
% 1.87/0.99      | m1_subset_1(sK0(sK3,X0_67,k2_relat_1(u1_waybel_0(sK3,sK5))),u1_struct_0(sK3)) != iProver_top ),
% 1.87/0.99      inference(demodulation,[status(thm)],[c_3096,c_3146]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3299,plain,
% 1.87/0.99      ( k1_waybel_9(sK3,sK5) = X0_67
% 1.87/0.99      | k2_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = X0_67
% 1.87/0.99      | r1_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_67) != iProver_top
% 1.87/0.99      | r1_orders_2(sK3,sK0(sK3,X0_67,k2_relat_1(u1_waybel_0(sK3,sK5))),sK4) = iProver_top
% 1.87/0.99      | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_2572,c_3289]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3305,plain,
% 1.87/0.99      ( k1_waybel_9(sK3,sK5) = X0_67
% 1.87/0.99      | r1_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),X0_67) != iProver_top
% 1.87/0.99      | r1_orders_2(sK3,sK0(sK3,X0_67,k2_relat_1(u1_waybel_0(sK3,sK5))),sK4) = iProver_top
% 1.87/0.99      | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top ),
% 1.87/0.99      inference(demodulation,[status(thm)],[c_3299,c_3146]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_7,plain,
% 1.87/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 1.87/0.99      | ~ r1_orders_2(X0,sK0(X0,X2,X1),X2)
% 1.87/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.87/0.99      | ~ v5_orders_2(X0)
% 1.87/0.99      | ~ l1_orders_2(X0)
% 1.87/0.99      | k2_yellow_0(X0,X1) = X2 ),
% 1.87/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1067,plain,
% 1.87/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 1.87/0.99      | ~ r1_orders_2(X0,sK0(X0,X2,X1),X2)
% 1.87/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.87/0.99      | ~ l1_orders_2(X0)
% 1.87/0.99      | k2_yellow_0(X0,X1) = X2
% 1.87/0.99      | sK3 != X0 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_34]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1068,plain,
% 1.87/0.99      ( ~ r1_lattice3(sK3,X0,X1)
% 1.87/0.99      | ~ r1_orders_2(sK3,sK0(sK3,X1,X0),X1)
% 1.87/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/0.99      | ~ l1_orders_2(sK3)
% 1.87/0.99      | k2_yellow_0(sK3,X0) = X1 ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_1067]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1072,plain,
% 1.87/0.99      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/0.99      | ~ r1_orders_2(sK3,sK0(sK3,X1,X0),X1)
% 1.87/0.99      | ~ r1_lattice3(sK3,X0,X1)
% 1.87/0.99      | k2_yellow_0(sK3,X0) = X1 ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_1068,c_30,c_74]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1073,plain,
% 1.87/0.99      ( ~ r1_lattice3(sK3,X0,X1)
% 1.87/0.99      | ~ r1_orders_2(sK3,sK0(sK3,X1,X0),X1)
% 1.87/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/0.99      | k2_yellow_0(sK3,X0) = X1 ),
% 1.87/0.99      inference(renaming,[status(thm)],[c_1072]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2116,plain,
% 1.87/0.99      ( ~ r1_lattice3(sK3,X0_69,X0_67)
% 1.87/0.99      | ~ r1_orders_2(sK3,sK0(sK3,X0_67,X0_69),X0_67)
% 1.87/0.99      | ~ m1_subset_1(X0_67,u1_struct_0(sK3))
% 1.87/0.99      | k2_yellow_0(sK3,X0_69) = X0_67 ),
% 1.87/0.99      inference(subtyping,[status(esa)],[c_1073]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2574,plain,
% 1.87/0.99      ( k2_yellow_0(sK3,X0_69) = X0_67
% 1.87/0.99      | r1_lattice3(sK3,X0_69,X0_67) != iProver_top
% 1.87/0.99      | r1_orders_2(sK3,sK0(sK3,X0_67,X0_69),X0_67) != iProver_top
% 1.87/0.99      | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_2116]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3507,plain,
% 1.87/0.99      ( k1_waybel_9(sK3,sK5) = sK4
% 1.87/0.99      | k2_yellow_0(sK3,k2_relat_1(u1_waybel_0(sK3,sK5))) = sK4
% 1.87/0.99      | r1_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),sK4) != iProver_top
% 1.87/0.99      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_3305,c_2574]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3512,plain,
% 1.87/0.99      ( k1_waybel_9(sK3,sK5) = sK4
% 1.87/0.99      | r1_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),sK4) != iProver_top
% 1.87/0.99      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 1.87/0.99      inference(demodulation,[status(thm)],[c_3507,c_3146]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_17,plain,
% 1.87/0.99      ( ~ v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0)
% 1.87/0.99      | ~ r3_waybel_9(X0,X1,X2)
% 1.87/0.99      | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
% 1.87/0.99      | ~ v11_waybel_0(X1,X0)
% 1.87/0.99      | ~ l1_waybel_0(X1,X0)
% 1.87/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.87/0.99      | ~ v2_pre_topc(X0)
% 1.87/0.99      | ~ v8_pre_topc(X0)
% 1.87/0.99      | ~ v3_orders_2(X0)
% 1.87/0.99      | ~ v2_lattice3(X0)
% 1.87/0.99      | ~ v1_compts_1(X0)
% 1.87/0.99      | ~ v4_orders_2(X1)
% 1.87/0.99      | ~ v4_orders_2(X0)
% 1.87/0.99      | ~ v7_waybel_0(X1)
% 1.87/0.99      | ~ l1_waybel_9(X0)
% 1.87/0.99      | ~ v5_orders_2(X0)
% 1.87/0.99      | ~ v1_lattice3(X0)
% 1.87/0.99      | v2_struct_0(X1) ),
% 1.87/0.99      inference(cnf_transformation,[],[f90]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_23,negated_conjecture,
% 1.87/0.99      ( v11_waybel_0(sK5,sK3) ),
% 1.87/0.99      inference(cnf_transformation,[],[f85]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_501,plain,
% 1.87/0.99      ( ~ v5_pre_topc(k4_waybel_1(X0,sK1(X0)),X0,X0)
% 1.87/0.99      | ~ r3_waybel_9(X0,X1,X2)
% 1.87/0.99      | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
% 1.87/0.99      | ~ l1_waybel_0(X1,X0)
% 1.87/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.87/0.99      | ~ v2_pre_topc(X0)
% 1.87/0.99      | ~ v8_pre_topc(X0)
% 1.87/0.99      | ~ v3_orders_2(X0)
% 1.87/0.99      | ~ v2_lattice3(X0)
% 1.87/0.99      | ~ v1_compts_1(X0)
% 1.87/0.99      | ~ v4_orders_2(X1)
% 1.87/0.99      | ~ v4_orders_2(X0)
% 1.87/0.99      | ~ v7_waybel_0(X1)
% 1.87/0.99      | ~ l1_waybel_9(X0)
% 1.87/0.99      | ~ v5_orders_2(X0)
% 1.87/0.99      | ~ v1_lattice3(X0)
% 1.87/0.99      | v2_struct_0(X1)
% 1.87/0.99      | sK5 != X1
% 1.87/0.99      | sK3 != X0 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_23]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_502,plain,
% 1.87/0.99      ( ~ v5_pre_topc(k4_waybel_1(sK3,sK1(sK3)),sK3,sK3)
% 1.87/0.99      | ~ r3_waybel_9(sK3,sK5,X0)
% 1.87/0.99      | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.87/0.99      | ~ l1_waybel_0(sK5,sK3)
% 1.87/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/0.99      | ~ v2_pre_topc(sK3)
% 1.87/0.99      | ~ v8_pre_topc(sK3)
% 1.87/0.99      | ~ v3_orders_2(sK3)
% 1.87/0.99      | ~ v2_lattice3(sK3)
% 1.87/0.99      | ~ v1_compts_1(sK3)
% 1.87/0.99      | ~ v4_orders_2(sK5)
% 1.87/0.99      | ~ v4_orders_2(sK3)
% 1.87/0.99      | ~ v7_waybel_0(sK5)
% 1.87/0.99      | ~ l1_waybel_9(sK3)
% 1.87/0.99      | ~ v5_orders_2(sK3)
% 1.87/0.99      | ~ v1_lattice3(sK3)
% 1.87/0.99      | v2_struct_0(sK5) ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_501]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_506,plain,
% 1.87/0.99      ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.87/0.99      | ~ r3_waybel_9(sK3,sK5,X0)
% 1.87/0.99      | ~ v5_pre_topc(k4_waybel_1(sK3,sK1(sK3)),sK3,sK3)
% 1.87/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_502,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_31,c_30,c_28,
% 1.87/0.99                 c_27,c_26,c_25]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_507,plain,
% 1.87/0.99      ( ~ v5_pre_topc(k4_waybel_1(sK3,sK1(sK3)),sK3,sK3)
% 1.87/0.99      | ~ r3_waybel_9(sK3,sK5,X0)
% 1.87/0.99      | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.87/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 1.87/0.99      inference(renaming,[status(thm)],[c_506]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_580,plain,
% 1.87/0.99      ( ~ r3_waybel_9(sK3,sK5,X0)
% 1.87/0.99      | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.87/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/0.99      | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X1)
% 1.87/0.99      | sK3 != sK3 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_507]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_918,plain,
% 1.87/0.99      ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.87/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.87/0.99      | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X1)
% 1.87/0.99      | sK4 != X0
% 1.87/0.99      | sK5 != sK5
% 1.87/0.99      | sK3 != sK3 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_580]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_919,plain,
% 1.87/0.99      ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
% 1.87/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/0.99      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 1.87/0.99      | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0) ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_918]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_923,plain,
% 1.87/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/0.99      | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
% 1.87/0.99      | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0) ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_919,c_29]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_924,plain,
% 1.87/0.99      ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
% 1.87/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/0.99      | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0) ),
% 1.87/0.99      inference(renaming,[status(thm)],[c_923]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2122,plain,
% 1.87/0.99      ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
% 1.87/0.99      | ~ m1_subset_1(X0_67,u1_struct_0(sK3))
% 1.87/0.99      | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0_67) ),
% 1.87/0.99      inference(subtyping,[status(esa)],[c_924]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2568,plain,
% 1.87/0.99      ( k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,X0_67)
% 1.87/0.99      | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) = iProver_top
% 1.87/0.99      | m1_subset_1(X0_67,u1_struct_0(sK3)) != iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_2122]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_18,plain,
% 1.87/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 1.87/0.99      | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
% 1.87/0.99      | ~ v11_waybel_0(X1,X0)
% 1.87/0.99      | ~ l1_waybel_0(X1,X0)
% 1.87/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.87/0.99      | m1_subset_1(sK1(X0),u1_struct_0(X0))
% 1.87/0.99      | ~ v2_pre_topc(X0)
% 1.87/0.99      | ~ v8_pre_topc(X0)
% 1.87/0.99      | ~ v3_orders_2(X0)
% 1.87/0.99      | ~ v2_lattice3(X0)
% 1.87/0.99      | ~ v1_compts_1(X0)
% 1.87/0.99      | ~ v4_orders_2(X1)
% 1.87/0.99      | ~ v4_orders_2(X0)
% 1.87/0.99      | ~ v7_waybel_0(X1)
% 1.87/0.99      | ~ l1_waybel_9(X0)
% 1.87/0.99      | ~ v5_orders_2(X0)
% 1.87/0.99      | ~ v1_lattice3(X0)
% 1.87/0.99      | v2_struct_0(X1) ),
% 1.87/0.99      inference(cnf_transformation,[],[f91]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_477,plain,
% 1.87/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 1.87/0.99      | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
% 1.87/0.99      | ~ l1_waybel_0(X1,X0)
% 1.87/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.87/0.99      | m1_subset_1(sK1(X0),u1_struct_0(X0))
% 1.87/0.99      | ~ v2_pre_topc(X0)
% 1.87/0.99      | ~ v8_pre_topc(X0)
% 1.87/0.99      | ~ v3_orders_2(X0)
% 1.87/0.99      | ~ v2_lattice3(X0)
% 1.87/0.99      | ~ v1_compts_1(X0)
% 1.87/0.99      | ~ v4_orders_2(X1)
% 1.87/0.99      | ~ v4_orders_2(X0)
% 1.87/0.99      | ~ v7_waybel_0(X1)
% 1.87/0.99      | ~ l1_waybel_9(X0)
% 1.87/0.99      | ~ v5_orders_2(X0)
% 1.87/0.99      | ~ v1_lattice3(X0)
% 1.87/0.99      | v2_struct_0(X1)
% 1.87/0.99      | sK5 != X1
% 1.87/0.99      | sK3 != X0 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_23]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_478,plain,
% 1.87/0.99      ( ~ r3_waybel_9(sK3,sK5,X0)
% 1.87/0.99      | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.87/0.99      | ~ l1_waybel_0(sK5,sK3)
% 1.87/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/0.99      | m1_subset_1(sK1(sK3),u1_struct_0(sK3))
% 1.87/0.99      | ~ v2_pre_topc(sK3)
% 1.87/0.99      | ~ v8_pre_topc(sK3)
% 1.87/0.99      | ~ v3_orders_2(sK3)
% 1.87/0.99      | ~ v2_lattice3(sK3)
% 1.87/0.99      | ~ v1_compts_1(sK3)
% 1.87/0.99      | ~ v4_orders_2(sK5)
% 1.87/0.99      | ~ v4_orders_2(sK3)
% 1.87/0.99      | ~ v7_waybel_0(sK5)
% 1.87/0.99      | ~ l1_waybel_9(sK3)
% 1.87/0.99      | ~ v5_orders_2(sK3)
% 1.87/0.99      | ~ v1_lattice3(sK3)
% 1.87/0.99      | v2_struct_0(sK5) ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_477]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_482,plain,
% 1.87/0.99      ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.87/0.99      | ~ r3_waybel_9(sK3,sK5,X0)
% 1.87/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/0.99      | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_478,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_31,c_30,c_28,
% 1.87/0.99                 c_27,c_26,c_25]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_483,plain,
% 1.87/0.99      ( ~ r3_waybel_9(sK3,sK5,X0)
% 1.87/0.99      | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.87/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/0.99      | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) ),
% 1.87/0.99      inference(renaming,[status(thm)],[c_482]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_939,plain,
% 1.87/0.99      ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),X0)
% 1.87/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.87/0.99      | m1_subset_1(sK1(sK3),u1_struct_0(sK3))
% 1.87/0.99      | sK4 != X0
% 1.87/0.99      | sK5 != sK5
% 1.87/0.99      | sK3 != sK3 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_483]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_940,plain,
% 1.87/0.99      ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
% 1.87/0.99      | m1_subset_1(sK1(sK3),u1_struct_0(sK3))
% 1.87/0.99      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_939]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_942,plain,
% 1.87/0.99      ( m1_subset_1(sK1(sK3),u1_struct_0(sK3))
% 1.87/0.99      | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_940,c_29]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_943,plain,
% 1.87/0.99      ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
% 1.87/0.99      | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) ),
% 1.87/0.99      inference(renaming,[status(thm)],[c_942]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_944,plain,
% 1.87/0.99      ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) = iProver_top
% 1.87/0.99      | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) = iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_943]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2140,plain,( X0_71 = X0_71 ),theory(equality) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2755,plain,
% 1.87/0.99      ( k4_waybel_1(sK3,sK1(sK3)) = k4_waybel_1(sK3,sK1(sK3)) ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_2140]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2756,plain,
% 1.87/0.99      ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4)
% 1.87/0.99      | ~ m1_subset_1(sK1(sK3),u1_struct_0(sK3))
% 1.87/0.99      | k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,sK1(sK3)) ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_2122]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2757,plain,
% 1.87/0.99      ( k4_waybel_1(sK3,sK1(sK3)) != k4_waybel_1(sK3,sK1(sK3))
% 1.87/0.99      | r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) = iProver_top
% 1.87/0.99      | m1_subset_1(sK1(sK3),u1_struct_0(sK3)) != iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_2756]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2795,plain,
% 1.87/0.99      ( r1_lattice3(sK3,k2_relset_1(u1_struct_0(sK5),u1_struct_0(sK3),u1_waybel_0(sK3,sK5)),sK4) = iProver_top ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_2568,c_944,c_2755,c_2757]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2875,plain,
% 1.87/0.99      ( r1_lattice3(sK3,k2_relat_1(u1_waybel_0(sK3,sK5)),sK4) = iProver_top ),
% 1.87/0.99      inference(demodulation,[status(thm)],[c_2822,c_2795]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_21,negated_conjecture,
% 1.87/0.99      ( k1_waybel_9(sK3,sK5) != sK4 ),
% 1.87/0.99      inference(cnf_transformation,[],[f87]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2129,negated_conjecture,
% 1.87/0.99      ( k1_waybel_9(sK3,sK5) != sK4 ),
% 1.87/0.99      inference(subtyping,[status(esa)],[c_21]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_48,plain,
% 1.87/0.99      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(contradiction,plain,
% 1.87/0.99      ( $false ),
% 1.87/0.99      inference(minisat,[status(thm)],[c_3512,c_2875,c_2129,c_48]) ).
% 1.87/0.99  
% 1.87/0.99  
% 1.87/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.87/0.99  
% 1.87/0.99  ------                               Statistics
% 1.87/0.99  
% 1.87/0.99  ------ General
% 1.87/0.99  
% 1.87/0.99  abstr_ref_over_cycles:                  0
% 1.87/0.99  abstr_ref_under_cycles:                 0
% 1.87/0.99  gc_basic_clause_elim:                   0
% 1.87/0.99  forced_gc_time:                         0
% 1.87/0.99  parsing_time:                           0.022
% 1.87/0.99  unif_index_cands_time:                  0.
% 1.87/0.99  unif_index_add_time:                    0.
% 1.87/0.99  orderings_time:                         0.
% 1.87/0.99  out_proof_time:                         0.019
% 1.87/0.99  total_time:                             0.159
% 1.87/0.99  num_of_symbols:                         75
% 1.87/0.99  num_of_terms:                           2344
% 1.87/0.99  
% 1.87/0.99  ------ Preprocessing
% 1.87/0.99  
% 1.87/0.99  num_of_splits:                          2
% 1.87/0.99  num_of_split_atoms:                     2
% 1.87/0.99  num_of_reused_defs:                     0
% 1.87/0.99  num_eq_ax_congr_red:                    28
% 1.87/0.99  num_of_sem_filtered_clauses:            1
% 1.87/0.99  num_of_subtypes:                        6
% 1.87/0.99  monotx_restored_types:                  0
% 1.87/0.99  sat_num_of_epr_types:                   0
% 1.87/0.99  sat_num_of_non_cyclic_types:            0
% 1.87/0.99  sat_guarded_non_collapsed_types:        1
% 1.87/0.99  num_pure_diseq_elim:                    0
% 1.87/0.99  simp_replaced_by:                       0
% 1.87/0.99  res_preprocessed:                       156
% 1.87/0.99  prep_upred:                             0
% 1.87/0.99  prep_unflattend:                        54
% 1.87/0.99  smt_new_axioms:                         0
% 1.87/0.99  pred_elim_cands:                        5
% 1.87/0.99  pred_elim:                              18
% 1.87/0.99  pred_elim_cl:                           19
% 1.87/0.99  pred_elim_cycles:                       26
% 1.87/0.99  merged_defs:                            0
% 1.87/0.99  merged_defs_ncl:                        0
% 1.87/0.99  bin_hyper_res:                          0
% 1.87/0.99  prep_cycles:                            4
% 1.87/0.99  pred_elim_time:                         0.033
% 1.87/0.99  splitting_time:                         0.
% 1.87/0.99  sem_filter_time:                        0.
% 1.87/0.99  monotx_time:                            0.
% 1.87/0.99  subtype_inf_time:                       0.
% 1.87/0.99  
% 1.87/0.99  ------ Problem properties
% 1.87/0.99  
% 1.87/0.99  clauses:                                22
% 1.87/0.99  conjectures:                            2
% 1.87/0.99  epr:                                    1
% 1.87/0.99  horn:                                   15
% 1.87/0.99  ground:                                 6
% 1.87/0.99  unary:                                  4
% 1.87/0.99  binary:                                 5
% 1.87/0.99  lits:                                   63
% 1.87/0.99  lits_eq:                                11
% 1.87/0.99  fd_pure:                                0
% 1.87/0.99  fd_pseudo:                              0
% 1.87/0.99  fd_cond:                                0
% 1.87/0.99  fd_pseudo_cond:                         3
% 1.87/0.99  ac_symbols:                             0
% 1.87/0.99  
% 1.87/0.99  ------ Propositional Solver
% 1.87/0.99  
% 1.87/0.99  prop_solver_calls:                      25
% 1.87/0.99  prop_fast_solver_calls:                 1563
% 1.87/0.99  smt_solver_calls:                       0
% 1.87/0.99  smt_fast_solver_calls:                  0
% 1.87/0.99  prop_num_of_clauses:                    821
% 1.87/0.99  prop_preprocess_simplified:             4459
% 1.87/0.99  prop_fo_subsumed:                       80
% 1.87/0.99  prop_solver_time:                       0.
% 1.87/0.99  smt_solver_time:                        0.
% 1.87/0.99  smt_fast_solver_time:                   0.
% 1.87/0.99  prop_fast_solver_time:                  0.
% 1.87/0.99  prop_unsat_core_time:                   0.
% 1.87/0.99  
% 1.87/0.99  ------ QBF
% 1.87/0.99  
% 1.87/0.99  qbf_q_res:                              0
% 1.87/0.99  qbf_num_tautologies:                    0
% 1.87/0.99  qbf_prep_cycles:                        0
% 1.87/0.99  
% 1.87/0.99  ------ BMC1
% 1.87/0.99  
% 1.87/0.99  bmc1_current_bound:                     -1
% 1.87/0.99  bmc1_last_solved_bound:                 -1
% 1.87/0.99  bmc1_unsat_core_size:                   -1
% 1.87/0.99  bmc1_unsat_core_parents_size:           -1
% 1.87/0.99  bmc1_merge_next_fun:                    0
% 1.87/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.87/0.99  
% 1.87/0.99  ------ Instantiation
% 1.87/0.99  
% 1.87/0.99  inst_num_of_clauses:                    197
% 1.87/0.99  inst_num_in_passive:                    4
% 1.87/0.99  inst_num_in_active:                     137
% 1.87/0.99  inst_num_in_unprocessed:                56
% 1.87/0.99  inst_num_of_loops:                      150
% 1.87/0.99  inst_num_of_learning_restarts:          0
% 1.87/0.99  inst_num_moves_active_passive:          10
% 1.87/0.99  inst_lit_activity:                      0
% 1.87/0.99  inst_lit_activity_moves:                0
% 1.87/0.99  inst_num_tautologies:                   0
% 1.87/0.99  inst_num_prop_implied:                  0
% 1.87/0.99  inst_num_existing_simplified:           0
% 1.87/0.99  inst_num_eq_res_simplified:             0
% 1.87/0.99  inst_num_child_elim:                    0
% 1.87/0.99  inst_num_of_dismatching_blockings:      15
% 1.87/0.99  inst_num_of_non_proper_insts:           141
% 1.87/0.99  inst_num_of_duplicates:                 0
% 1.87/0.99  inst_inst_num_from_inst_to_res:         0
% 1.87/0.99  inst_dismatching_checking_time:         0.
% 1.87/0.99  
% 1.87/0.99  ------ Resolution
% 1.87/0.99  
% 1.87/0.99  res_num_of_clauses:                     0
% 1.87/0.99  res_num_in_passive:                     0
% 1.87/0.99  res_num_in_active:                      0
% 1.87/0.99  res_num_of_loops:                       160
% 1.87/0.99  res_forward_subset_subsumed:            34
% 1.87/0.99  res_backward_subset_subsumed:           0
% 1.87/0.99  res_forward_subsumed:                   0
% 1.87/0.99  res_backward_subsumed:                  0
% 1.87/0.99  res_forward_subsumption_resolution:     2
% 1.87/0.99  res_backward_subsumption_resolution:    0
% 1.87/0.99  res_clause_to_clause_subsumption:       116
% 1.87/0.99  res_orphan_elimination:                 0
% 1.87/0.99  res_tautology_del:                      16
% 1.87/0.99  res_num_eq_res_simplified:              0
% 1.87/0.99  res_num_sel_changes:                    0
% 1.87/0.99  res_moves_from_active_to_pass:          0
% 1.87/0.99  
% 1.87/0.99  ------ Superposition
% 1.87/0.99  
% 1.87/0.99  sup_time_total:                         0.
% 1.87/0.99  sup_time_generating:                    0.
% 1.87/0.99  sup_time_sim_full:                      0.
% 1.87/0.99  sup_time_sim_immed:                     0.
% 1.87/0.99  
% 1.87/0.99  sup_num_of_clauses:                     34
% 1.87/0.99  sup_num_in_active:                      28
% 1.87/0.99  sup_num_in_passive:                     6
% 1.87/0.99  sup_num_of_loops:                       29
% 1.87/0.99  sup_fw_superposition:                   10
% 1.87/0.99  sup_bw_superposition:                   7
% 1.87/0.99  sup_immediate_simplified:               9
% 1.87/0.99  sup_given_eliminated:                   0
% 1.87/0.99  comparisons_done:                       0
% 1.87/0.99  comparisons_avoided:                    0
% 1.87/0.99  
% 1.87/0.99  ------ Simplifications
% 1.87/0.99  
% 1.87/0.99  
% 1.87/0.99  sim_fw_subset_subsumed:                 0
% 1.87/0.99  sim_bw_subset_subsumed:                 3
% 1.87/0.99  sim_fw_subsumed:                        2
% 1.87/0.99  sim_bw_subsumed:                        0
% 1.87/0.99  sim_fw_subsumption_res:                 0
% 1.87/0.99  sim_bw_subsumption_res:                 0
% 1.87/0.99  sim_tautology_del:                      1
% 1.87/0.99  sim_eq_tautology_del:                   0
% 1.87/0.99  sim_eq_res_simp:                        0
% 1.87/0.99  sim_fw_demodulated:                     4
% 1.87/0.99  sim_bw_demodulated:                     1
% 1.87/0.99  sim_light_normalised:                   4
% 1.87/0.99  sim_joinable_taut:                      0
% 1.87/0.99  sim_joinable_simp:                      0
% 1.87/0.99  sim_ac_normalised:                      0
% 1.87/0.99  sim_smt_subsumption:                    0
% 1.87/0.99  
%------------------------------------------------------------------------------
