%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1485+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:44 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 728 expanded)
%              Number of clauses        :  109 ( 193 expanded)
%              Number of leaves         :   20 ( 219 expanded)
%              Depth                    :   18
%              Number of atoms          : 1079 (4760 expanded)
%              Number of equality atoms :  181 ( 705 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   21 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,sK6)) != X1
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k12_lattice3(X0,sK5,k13_lattice3(X0,sK5,X2)) != sK5
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k12_lattice3(sK4,X1,k13_lattice3(sK4,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(sK4)) )
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & l1_orders_2(sK4)
      & v2_lattice3(sK4)
      & v1_lattice3(sK4)
      & v5_orders_2(sK4)
      & v3_orders_2(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( k12_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) != sK5
    & m1_subset_1(sK6,u1_struct_0(sK4))
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l1_orders_2(sK4)
    & v2_lattice3(sK4)
    & v1_lattice3(sK4)
    & v5_orders_2(sK4)
    & v3_orders_2(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f32,f50,f49,f48])).

fof(f82,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k10_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X2,X4)
                              & r1_orders_2(X0,X1,X4) )
                           => r1_orders_2(X0,X3,X4) ) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k10_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k10_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X3,X4)
                            | ~ r1_orders_2(X0,X2,X4)
                            | ~ r1_orders_2(X0,X1,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X3,X4)
                            | ~ r1_orders_2(X0,X2,X4)
                            | ~ r1_orders_2(X0,X1,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK3(X0,X1,X2,X3))
        & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3))
        & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3))
        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,X3,sK3(X0,X1,X2,X3))
                        & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3))
                        & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3))
                        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f45])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f81,plain,(
    v2_lattice3(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f79,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f80,plain,(
    v1_lattice3(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v5_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ? [X3] :
                      ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( k11_lattice3(X0,X1,X2) = X3
                      <=> ( ! [X4] :
                              ( m1_subset_1(X4,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X4,X2)
                                  & r1_orders_2(X0,X4,X1) )
                               => r1_orders_2(X0,X4,X3) ) )
                          & r1_orders_2(X0,X3,X2)
                          & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v5_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ? [X3] :
                      ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X0))
                     => ( k11_lattice3(X0,X1,X2) = X5
                      <=> ( ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X6,X2)
                                  & r1_orders_2(X0,X6,X1) )
                               => r1_orders_2(X0,X6,X5) ) )
                          & r1_orders_2(X0,X5,X2)
                          & r1_orders_2(X0,X5,X1) ) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f2])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X5] :
                  ( ( k11_lattice3(X0,X1,X2) = X5
                  <=> ( ! [X6] :
                          ( r1_orders_2(X0,X6,X5)
                          | ~ r1_orders_2(X0,X6,X2)
                          | ~ r1_orders_2(X0,X6,X1)
                          | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X5,X2)
                      & r1_orders_2(X0,X5,X1) ) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_orders_2(X0,X4,X2)
                      & r1_orders_2(X0,X4,X1)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X3,X2)
                  | ~ r1_orders_2(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X5] :
                  ( ( k11_lattice3(X0,X1,X2) = X5
                  <=> ( ! [X6] :
                          ( r1_orders_2(X0,X6,X5)
                          | ~ r1_orders_2(X0,X6,X2)
                          | ~ r1_orders_2(X0,X6,X1)
                          | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X5,X2)
                      & r1_orders_2(X0,X5,X1) ) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_orders_2(X0,X4,X2)
                      & r1_orders_2(X0,X4,X1)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X3,X2)
                  | ~ r1_orders_2(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f33,plain,(
    ! [X0,X2,X1] :
      ( ! [X5] :
          ( ( k11_lattice3(X0,X1,X2) = X5
          <=> ( ! [X6] :
                  ( r1_orders_2(X0,X6,X5)
                  | ~ r1_orders_2(X0,X6,X2)
                  | ~ r1_orders_2(X0,X6,X1)
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              & r1_orders_2(X0,X5,X2)
              & r1_orders_2(X0,X5,X1) ) )
          | ~ m1_subset_1(X5,u1_struct_0(X0)) )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP0(X0,X2,X1)
              | ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_orders_2(X0,X4,X2)
                      & r1_orders_2(X0,X4,X1)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X3,X2)
                  | ~ r1_orders_2(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f16,f33])).

fof(f40,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK2(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK2(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK2(X0,X1,X2,X3),X1)
        & m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP0(X0,X2,X1)
              | ! [X3] :
                  ( ( ~ r1_orders_2(X0,sK2(X0,X1,X2,X3),X3)
                    & r1_orders_2(X0,sK2(X0,X1,X2,X3),X2)
                    & r1_orders_2(X0,sK2(X0,X1,X2,X3),X1)
                    & m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X3,X2)
                  | ~ r1_orders_2(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f40])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X2,X1)
      | r1_orders_2(X0,sK2(X0,X1,X2,X3),X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X2,X1)
      | ~ r1_orders_2(X0,sK2(X0,X1,X2,X3),X3)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f35,plain,(
    ! [X0,X2,X1] :
      ( ! [X5] :
          ( ( ( k11_lattice3(X0,X1,X2) = X5
              | ? [X6] :
                  ( ~ r1_orders_2(X0,X6,X5)
                  & r1_orders_2(X0,X6,X2)
                  & r1_orders_2(X0,X6,X1)
                  & m1_subset_1(X6,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X5,X2)
              | ~ r1_orders_2(X0,X5,X1) )
            & ( ( ! [X6] :
                    ( r1_orders_2(X0,X6,X5)
                    | ~ r1_orders_2(X0,X6,X2)
                    | ~ r1_orders_2(X0,X6,X1)
                    | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                & r1_orders_2(X0,X5,X2)
                & r1_orders_2(X0,X5,X1) )
              | k11_lattice3(X0,X1,X2) != X5 ) )
          | ~ m1_subset_1(X5,u1_struct_0(X0)) )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f36,plain,(
    ! [X0,X2,X1] :
      ( ! [X5] :
          ( ( ( k11_lattice3(X0,X1,X2) = X5
              | ? [X6] :
                  ( ~ r1_orders_2(X0,X6,X5)
                  & r1_orders_2(X0,X6,X2)
                  & r1_orders_2(X0,X6,X1)
                  & m1_subset_1(X6,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X5,X2)
              | ~ r1_orders_2(X0,X5,X1) )
            & ( ( ! [X6] :
                    ( r1_orders_2(X0,X6,X5)
                    | ~ r1_orders_2(X0,X6,X2)
                    | ~ r1_orders_2(X0,X6,X1)
                    | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                & r1_orders_2(X0,X5,X2)
                & r1_orders_2(X0,X5,X1) )
              | k11_lattice3(X0,X1,X2) != X5 ) )
          | ~ m1_subset_1(X5,u1_struct_0(X0)) )
      | ~ sP0(X0,X2,X1) ) ),
    inference(flattening,[],[f35])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( k11_lattice3(X0,X2,X1) = X3
              | ? [X4] :
                  ( ~ r1_orders_2(X0,X4,X3)
                  & r1_orders_2(X0,X4,X1)
                  & r1_orders_2(X0,X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X3,X1)
              | ~ r1_orders_2(X0,X3,X2) )
            & ( ( ! [X5] :
                    ( r1_orders_2(X0,X5,X3)
                    | ~ r1_orders_2(X0,X5,X1)
                    | ~ r1_orders_2(X0,X5,X2)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_orders_2(X0,X3,X1)
                & r1_orders_2(X0,X3,X2) )
              | k11_lattice3(X0,X2,X1) != X3 ) )
          | ~ m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X1)
          & r1_orders_2(X0,X4,X2)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK1(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK1(X0,X1,X2,X3),X1)
        & r1_orders_2(X0,sK1(X0,X1,X2,X3),X2)
        & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( k11_lattice3(X0,X2,X1) = X3
              | ( ~ r1_orders_2(X0,sK1(X0,X1,X2,X3),X3)
                & r1_orders_2(X0,sK1(X0,X1,X2,X3),X1)
                & r1_orders_2(X0,sK1(X0,X1,X2,X3),X2)
                & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X3,X1)
              | ~ r1_orders_2(X0,X3,X2) )
            & ( ( ! [X5] :
                    ( r1_orders_2(X0,X5,X3)
                    | ~ r1_orders_2(X0,X5,X1)
                    | ~ r1_orders_2(X0,X5,X2)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_orders_2(X0,X3,X1)
                & r1_orders_2(X0,X3,X2) )
              | k11_lattice3(X0,X2,X1) != X3 ) )
          | ~ m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X2,X1) = X3
      | ~ r1_orders_2(X0,sK1(X0,X1,X2,X3),X3)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X2,X1) = X3
      | r1_orders_2(X0,sK1(X0,X1,X2,X3),X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f78,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f85,plain,(
    k12_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) != sK5 ),
    inference(cnf_transformation,[],[f51])).

fof(f84,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k10_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_29,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_953,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k10_lattice3(X1,X2,X0),u1_struct_0(X1))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_29])).

cnf(c_954,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(k10_lattice3(sK4,X0,X1),u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_953])).

cnf(c_20,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_30,negated_conjecture,
    ( v2_lattice3(sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_351,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_30])).

cnf(c_352,plain,
    ( ~ l1_orders_2(sK4)
    | ~ v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_351])).

cnf(c_105,plain,
    ( ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4)
    | ~ v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_354,plain,
    ( ~ v2_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_352,c_30,c_29,c_105])).

cnf(c_488,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_354])).

cnf(c_489,plain,
    ( r1_orders_2(sK4,X0,k10_lattice3(sK4,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k10_lattice3(sK4,X0,X1),u1_struct_0(sK4))
    | ~ v1_lattice3(sK4)
    | ~ v5_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_488])).

cnf(c_32,negated_conjecture,
    ( v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_31,negated_conjecture,
    ( v1_lattice3(sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_493,plain,
    ( ~ m1_subset_1(k10_lattice3(sK4,X0,X1),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r1_orders_2(sK4,X0,k10_lattice3(sK4,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_489,c_32,c_31,c_29])).

cnf(c_494,plain,
    ( r1_orders_2(sK4,X0,k10_lattice3(sK4,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(k10_lattice3(sK4,X0,X1),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_493])).

cnf(c_972,plain,
    ( r1_orders_2(sK4,X0,k10_lattice3(sK4,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_954,c_494])).

cnf(c_3232,plain,
    ( r1_orders_2(sK4,X0_50,k10_lattice3(sK4,X0_50,X1_50))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_972])).

cnf(c_6947,plain,
    ( r1_orders_2(sK4,sK5,k10_lattice3(sK4,sK5,sK6))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3232])).

cnf(c_6950,plain,
    ( r1_orders_2(sK4,sK5,k10_lattice3(sK4,sK5,sK6)) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6947])).

cnf(c_3263,plain,
    ( ~ r1_orders_2(X0_49,X0_50,X1_50)
    | r1_orders_2(X0_49,X2_50,X3_50)
    | X2_50 != X0_50
    | X3_50 != X1_50 ),
    theory(equality)).

cnf(c_5930,plain,
    ( ~ r1_orders_2(sK4,X0_50,X1_50)
    | r1_orders_2(sK4,X2_50,k13_lattice3(sK4,sK5,sK6))
    | X2_50 != X0_50
    | k13_lattice3(sK4,sK5,sK6) != X1_50 ),
    inference(instantiation,[status(thm)],[c_3263])).

cnf(c_6823,plain,
    ( r1_orders_2(sK4,X0_50,k13_lattice3(sK4,sK5,sK6))
    | ~ r1_orders_2(sK4,X1_50,k10_lattice3(sK4,sK5,sK6))
    | X0_50 != X1_50
    | k13_lattice3(sK4,sK5,sK6) != k10_lattice3(sK4,sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_5930])).

cnf(c_6824,plain,
    ( X0_50 != X1_50
    | k13_lattice3(sK4,sK5,sK6) != k10_lattice3(sK4,sK5,sK6)
    | r1_orders_2(sK4,X0_50,k13_lattice3(sK4,sK5,sK6)) = iProver_top
    | r1_orders_2(sK4,X1_50,k10_lattice3(sK4,sK5,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6823])).

cnf(c_6826,plain,
    ( k13_lattice3(sK4,sK5,sK6) != k10_lattice3(sK4,sK5,sK6)
    | sK5 != sK5
    | r1_orders_2(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) = iProver_top
    | r1_orders_2(sK4,sK5,k10_lattice3(sK4,sK5,sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6824])).

cnf(c_10,plain,
    ( sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X3,X1)
    | r1_orders_2(X0,sK2(X0,X2,X1,X3),X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_826,plain,
    ( sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X3,X1)
    | r1_orders_2(X0,sK2(X0,X2,X1,X3),X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_32])).

cnf(c_827,plain,
    ( sP0(sK4,X0,X1)
    | ~ r1_orders_2(sK4,X2,X1)
    | ~ r1_orders_2(sK4,X2,X0)
    | r1_orders_2(sK4,sK2(sK4,X1,X0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_826])).

cnf(c_831,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r1_orders_2(sK4,sK2(sK4,X1,X0,X2),X1)
    | ~ r1_orders_2(sK4,X2,X0)
    | ~ r1_orders_2(sK4,X2,X1)
    | sP0(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_827,c_29])).

cnf(c_832,plain,
    ( sP0(sK4,X0,X1)
    | ~ r1_orders_2(sK4,X2,X1)
    | ~ r1_orders_2(sK4,X2,X0)
    | r1_orders_2(sK4,sK2(sK4,X1,X0,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_831])).

cnf(c_3237,plain,
    ( sP0(sK4,X0_50,X1_50)
    | ~ r1_orders_2(sK4,X2_50,X1_50)
    | ~ r1_orders_2(sK4,X2_50,X0_50)
    | r1_orders_2(sK4,sK2(sK4,X1_50,X0_50,X2_50),X1_50)
    | ~ m1_subset_1(X2_50,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_832])).

cnf(c_5380,plain,
    ( sP0(sK4,k13_lattice3(sK4,sK5,sK6),sK5)
    | ~ r1_orders_2(sK4,X0_50,k13_lattice3(sK4,sK5,sK6))
    | ~ r1_orders_2(sK4,X0_50,sK5)
    | r1_orders_2(sK4,sK2(sK4,sK5,k13_lattice3(sK4,sK5,sK6),X0_50),sK5)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | ~ m1_subset_1(k13_lattice3(sK4,sK5,sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3237])).

cnf(c_5396,plain,
    ( sP0(sK4,k13_lattice3(sK4,sK5,sK6),sK5) = iProver_top
    | r1_orders_2(sK4,X0_50,k13_lattice3(sK4,sK5,sK6)) != iProver_top
    | r1_orders_2(sK4,X0_50,sK5) != iProver_top
    | r1_orders_2(sK4,sK2(sK4,sK5,k13_lattice3(sK4,sK5,sK6),X0_50),sK5) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k13_lattice3(sK4,sK5,sK6),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5380])).

cnf(c_5398,plain,
    ( sP0(sK4,k13_lattice3(sK4,sK5,sK6),sK5) = iProver_top
    | r1_orders_2(sK4,sK2(sK4,sK5,k13_lattice3(sK4,sK5,sK6),sK5),sK5) = iProver_top
    | r1_orders_2(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) != iProver_top
    | r1_orders_2(sK4,sK5,sK5) != iProver_top
    | m1_subset_1(k13_lattice3(sK4,sK5,sK6),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5396])).

cnf(c_8,plain,
    ( sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X3,X1)
    | ~ r1_orders_2(X0,sK2(X0,X2,X1,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_888,plain,
    ( sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X3,X1)
    | ~ r1_orders_2(X0,sK2(X0,X2,X1,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_32])).

cnf(c_889,plain,
    ( sP0(sK4,X0,X1)
    | ~ r1_orders_2(sK4,X2,X1)
    | ~ r1_orders_2(sK4,X2,X0)
    | ~ r1_orders_2(sK4,sK2(sK4,X1,X0,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_888])).

cnf(c_893,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r1_orders_2(sK4,sK2(sK4,X1,X0,X2),X2)
    | ~ r1_orders_2(sK4,X2,X0)
    | ~ r1_orders_2(sK4,X2,X1)
    | sP0(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_889,c_29])).

cnf(c_894,plain,
    ( sP0(sK4,X0,X1)
    | ~ r1_orders_2(sK4,X2,X1)
    | ~ r1_orders_2(sK4,X2,X0)
    | ~ r1_orders_2(sK4,sK2(sK4,X1,X0,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_893])).

cnf(c_3235,plain,
    ( sP0(sK4,X0_50,X1_50)
    | ~ r1_orders_2(sK4,X2_50,X1_50)
    | ~ r1_orders_2(sK4,X2_50,X0_50)
    | ~ r1_orders_2(sK4,sK2(sK4,X1_50,X0_50,X2_50),X2_50)
    | ~ m1_subset_1(X2_50,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_894])).

cnf(c_5382,plain,
    ( sP0(sK4,k13_lattice3(sK4,sK5,sK6),sK5)
    | ~ r1_orders_2(sK4,X0_50,k13_lattice3(sK4,sK5,sK6))
    | ~ r1_orders_2(sK4,X0_50,sK5)
    | ~ r1_orders_2(sK4,sK2(sK4,sK5,k13_lattice3(sK4,sK5,sK6),X0_50),X0_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | ~ m1_subset_1(k13_lattice3(sK4,sK5,sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3235])).

cnf(c_5388,plain,
    ( sP0(sK4,k13_lattice3(sK4,sK5,sK6),sK5) = iProver_top
    | r1_orders_2(sK4,X0_50,k13_lattice3(sK4,sK5,sK6)) != iProver_top
    | r1_orders_2(sK4,X0_50,sK5) != iProver_top
    | r1_orders_2(sK4,sK2(sK4,sK5,k13_lattice3(sK4,sK5,sK6),X0_50),X0_50) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k13_lattice3(sK4,sK5,sK6),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5382])).

cnf(c_5390,plain,
    ( sP0(sK4,k13_lattice3(sK4,sK5,sK6),sK5) = iProver_top
    | r1_orders_2(sK4,sK2(sK4,sK5,k13_lattice3(sK4,sK5,sK6),sK5),sK5) != iProver_top
    | r1_orders_2(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) != iProver_top
    | r1_orders_2(sK4,sK5,sK5) != iProver_top
    | m1_subset_1(k13_lattice3(sK4,sK5,sK6),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5388])).

cnf(c_1,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X1)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,sK1(X0,X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | k11_lattice3(X0,X2,X1) = X3 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_3256,plain,
    ( ~ sP0(X0_49,X0_50,X1_50)
    | ~ r1_orders_2(X0_49,X2_50,X0_50)
    | ~ r1_orders_2(X0_49,X2_50,X1_50)
    | ~ r1_orders_2(X0_49,sK1(X0_49,X0_50,X1_50,X2_50),X2_50)
    | ~ m1_subset_1(X2_50,u1_struct_0(X0_49))
    | k11_lattice3(X0_49,X1_50,X0_50) = X2_50 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_4277,plain,
    ( ~ sP0(sK4,k13_lattice3(sK4,sK5,sK6),sK5)
    | ~ r1_orders_2(sK4,X0_50,k13_lattice3(sK4,sK5,sK6))
    | ~ r1_orders_2(sK4,X0_50,sK5)
    | ~ r1_orders_2(sK4,sK1(sK4,k13_lattice3(sK4,sK5,sK6),sK5,X0_50),X0_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | k11_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) = X0_50 ),
    inference(instantiation,[status(thm)],[c_3256])).

cnf(c_4293,plain,
    ( k11_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) = X0_50
    | sP0(sK4,k13_lattice3(sK4,sK5,sK6),sK5) != iProver_top
    | r1_orders_2(sK4,X0_50,k13_lattice3(sK4,sK5,sK6)) != iProver_top
    | r1_orders_2(sK4,X0_50,sK5) != iProver_top
    | r1_orders_2(sK4,sK1(sK4,k13_lattice3(sK4,sK5,sK6),sK5,X0_50),X0_50) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4277])).

cnf(c_4295,plain,
    ( k11_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) = sK5
    | sP0(sK4,k13_lattice3(sK4,sK5,sK6),sK5) != iProver_top
    | r1_orders_2(sK4,sK1(sK4,k13_lattice3(sK4,sK5,sK6),sK5,sK5),sK5) != iProver_top
    | r1_orders_2(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) != iProver_top
    | r1_orders_2(sK4,sK5,sK5) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4293])).

cnf(c_3,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X1)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,sK1(X0,X1,X2,X3),X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | k11_lattice3(X0,X2,X1) = X3 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_3254,plain,
    ( ~ sP0(X0_49,X0_50,X1_50)
    | ~ r1_orders_2(X0_49,X2_50,X0_50)
    | ~ r1_orders_2(X0_49,X2_50,X1_50)
    | r1_orders_2(X0_49,sK1(X0_49,X0_50,X1_50,X2_50),X1_50)
    | ~ m1_subset_1(X2_50,u1_struct_0(X0_49))
    | k11_lattice3(X0_49,X1_50,X0_50) = X2_50 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_4279,plain,
    ( ~ sP0(sK4,k13_lattice3(sK4,sK5,sK6),sK5)
    | ~ r1_orders_2(sK4,X0_50,k13_lattice3(sK4,sK5,sK6))
    | ~ r1_orders_2(sK4,X0_50,sK5)
    | r1_orders_2(sK4,sK1(sK4,k13_lattice3(sK4,sK5,sK6),sK5,X0_50),sK5)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | k11_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) = X0_50 ),
    inference(instantiation,[status(thm)],[c_3254])).

cnf(c_4285,plain,
    ( k11_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) = X0_50
    | sP0(sK4,k13_lattice3(sK4,sK5,sK6),sK5) != iProver_top
    | r1_orders_2(sK4,X0_50,k13_lattice3(sK4,sK5,sK6)) != iProver_top
    | r1_orders_2(sK4,X0_50,sK5) != iProver_top
    | r1_orders_2(sK4,sK1(sK4,k13_lattice3(sK4,sK5,sK6),sK5,X0_50),sK5) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4279])).

cnf(c_4287,plain,
    ( k11_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) = sK5
    | sP0(sK4,k13_lattice3(sK4,sK5,sK6),sK5) != iProver_top
    | r1_orders_2(sK4,sK1(sK4,k13_lattice3(sK4,sK5,sK6),sK5,sK5),sK5) = iProver_top
    | r1_orders_2(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) != iProver_top
    | r1_orders_2(sK4,sK5,sK5) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4285])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k13_lattice3(X1,X2,X0) = k10_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_743,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k13_lattice3(X1,X2,X0) = k10_lattice3(X1,X2,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_31])).

cnf(c_744,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ v5_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | k13_lattice3(sK4,X0,X1) = k10_lattice3(sK4,X0,X1) ),
    inference(unflattening,[status(thm)],[c_743])).

cnf(c_748,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | k13_lattice3(sK4,X0,X1) = k10_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_744,c_32,c_29])).

cnf(c_3240,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK4))
    | k13_lattice3(sK4,X0_50,X1_50) = k10_lattice3(sK4,X0_50,X1_50) ),
    inference(subtyping,[status(esa)],[c_748])).

cnf(c_4181,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | k13_lattice3(sK4,sK5,sK6) = k10_lattice3(sK4,sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_3240])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k13_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_764,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k13_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_31])).

cnf(c_765,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(k13_lattice3(sK4,X0,X1),u1_struct_0(sK4))
    | ~ v5_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_764])).

cnf(c_769,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(k13_lattice3(sK4,X0,X1),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_765,c_32,c_29])).

cnf(c_3239,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK4))
    | m1_subset_1(k13_lattice3(sK4,X0_50,X1_50),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_769])).

cnf(c_4165,plain,
    ( m1_subset_1(k13_lattice3(sK4,sK5,sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3239])).

cnf(c_4166,plain,
    ( m1_subset_1(k13_lattice3(sK4,sK5,sK6),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4165])).

cnf(c_3262,plain,
    ( X0_50 != X1_50
    | X2_50 != X1_50
    | X2_50 = X0_50 ),
    theory(equality)).

cnf(c_4137,plain,
    ( k11_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) != X0_50
    | sK5 != X0_50
    | sK5 = k11_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_3262])).

cnf(c_4138,plain,
    ( k11_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) != sK5
    | sK5 = k11_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_4137])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_362,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_30])).

cnf(c_363,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ v5_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | k12_lattice3(sK4,X0,X1) = k11_lattice3(sK4,X0,X1) ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_367,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | k12_lattice3(sK4,X0,X1) = k11_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_363,c_32,c_29])).

cnf(c_3246,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK4))
    | k12_lattice3(sK4,X0_50,X1_50) = k11_lattice3(sK4,X0_50,X1_50) ),
    inference(subtyping,[status(esa)],[c_367])).

cnf(c_4095,plain,
    ( ~ m1_subset_1(k13_lattice3(sK4,sK5,sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | k12_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) = k11_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_3246])).

cnf(c_4071,plain,
    ( k12_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) != X0_50
    | k12_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) = sK5
    | sK5 != X0_50 ),
    inference(instantiation,[status(thm)],[c_3262])).

cnf(c_4094,plain,
    ( k12_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) != k11_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6))
    | k12_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) = sK5
    | sK5 != k11_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_4071])).

cnf(c_25,plain,
    ( r3_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_33,negated_conjecture,
    ( v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_389,plain,
    ( r3_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_33])).

cnf(c_390,plain,
    ( r3_orders_2(sK4,X0,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_389])).

cnf(c_394,plain,
    ( r3_orders_2(sK4,X0,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_390,c_30,c_29,c_105])).

cnf(c_395,plain,
    ( r3_orders_2(sK4,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_394])).

cnf(c_24,plain,
    ( ~ r3_orders_2(X0,X1,X2)
    | r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_410,plain,
    ( ~ r3_orders_2(X0,X1,X2)
    | r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_33])).

cnf(c_411,plain,
    ( ~ r3_orders_2(sK4,X0,X1)
    | r1_orders_2(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_415,plain,
    ( ~ r3_orders_2(sK4,X0,X1)
    | r1_orders_2(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_411,c_30,c_29,c_105])).

cnf(c_416,plain,
    ( ~ r3_orders_2(sK4,X0,X1)
    | r1_orders_2(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_415])).

cnf(c_469,plain,
    ( r1_orders_2(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X3,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | X0 != X2
    | X1 != X2
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_395,c_416])).

cnf(c_470,plain,
    ( r1_orders_2(sK4,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_469])).

cnf(c_3245,plain,
    ( r1_orders_2(sK4,X0_50,X0_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_470])).

cnf(c_3257,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_3245])).

cnf(c_3299,plain,
    ( m1_subset_1(X0_50,u1_struct_0(sK4)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3257])).

cnf(c_3301,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_3299])).

cnf(c_3258,plain,
    ( r1_orders_2(sK4,X0_50,X0_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK4))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_3245])).

cnf(c_3296,plain,
    ( r1_orders_2(sK4,X0_50,X0_50) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK4)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3258])).

cnf(c_3298,plain,
    ( r1_orders_2(sK4,sK5,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_3296])).

cnf(c_3259,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_3245])).

cnf(c_3295,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3259])).

cnf(c_26,negated_conjecture,
    ( k12_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) != sK5 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3249,negated_conjecture,
    ( k12_lattice3(sK4,sK5,k13_lattice3(sK4,sK5,sK6)) != sK5 ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_3261,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_3272,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_3261])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_40,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_39,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6950,c_6826,c_5398,c_5390,c_4295,c_4287,c_4181,c_4166,c_4165,c_4138,c_4095,c_4094,c_3301,c_3298,c_3295,c_3249,c_3272,c_40,c_27,c_39,c_28])).


%------------------------------------------------------------------------------
