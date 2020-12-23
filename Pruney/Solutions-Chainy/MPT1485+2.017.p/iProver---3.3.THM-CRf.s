%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:06 EST 2020

% Result     : Theorem 1.10s
% Output     : CNFRefutation 1.10s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 813 expanded)
%              Number of clauses        :  104 ( 212 expanded)
%              Number of leaves         :   16 ( 246 expanded)
%              Depth                    :   19
%              Number of atoms          :  977 (5222 expanded)
%              Number of equality atoms :  170 ( 797 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   21 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
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

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,sK4)) != X1
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k12_lattice3(X0,sK3,k13_lattice3(X0,sK3,X2)) != sK3
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
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
              ( k12_lattice3(sK2,X1,k13_lattice3(sK2,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_orders_2(sK2)
      & v2_lattice3(sK2)
      & v1_lattice3(sK2)
      & v5_orders_2(sK2)
      & v3_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_orders_2(sK2)
    & v2_lattice3(sK2)
    & v1_lattice3(sK2)
    & v5_orders_2(sK2)
    & v3_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f28,f42,f41,f40])).

fof(f71,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f43])).

fof(f70,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f69,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f66,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f67,plain,(
    v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f43])).

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

fof(f19,plain,(
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

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK0(X0,X1,X2,X3))
        & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3))
        & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3))
        & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,X3,sK0(X0,X1,X2,X3))
                        & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3))
                        & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3))
                        & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f49,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f68,plain,(
    v2_lattice3(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK1(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK1(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK1(X0,X1,X2,X3),X1)
        & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,sK1(X0,X1,X2,X3),X3)
                        & r1_orders_2(X0,sK1(X0,X1,X2,X3),X2)
                        & r1_orders_2(X0,sK1(X0,X1,X2,X3),X1)
                        & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,sK1(X0,X1,X2,X3),X3)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X1,X2) = X3
      | r1_orders_2(X0,sK1(X0,X1,X2,X3),X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f65,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f72,plain,(
    k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1190,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1572,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1190])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1189,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1573,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1189])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_24,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_989,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_24])).

cnf(c_990,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ v1_lattice3(sK2)
    | k10_lattice3(sK2,X0,X1) = k13_lattice3(sK2,X0,X1) ),
    inference(unflattening,[status(thm)],[c_989])).

cnf(c_27,negated_conjecture,
    ( v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_26,negated_conjecture,
    ( v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_994,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k10_lattice3(sK2,X0,X1) = k13_lattice3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_990,c_27,c_26])).

cnf(c_995,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k10_lattice3(sK2,X1,X0) = k13_lattice3(sK2,X1,X0) ),
    inference(renaming,[status(thm)],[c_994])).

cnf(c_1172,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | k10_lattice3(sK2,X1_47,X0_47) = k13_lattice3(sK2,X1_47,X0_47) ),
    inference(subtyping,[status(esa)],[c_995])).

cnf(c_1592,plain,
    ( k10_lattice3(sK2,X0_47,X1_47) = k13_lattice3(sK2,X0_47,X1_47)
    | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1172])).

cnf(c_2143,plain,
    ( k10_lattice3(sK2,sK3,X0_47) = k13_lattice3(sK2,sK3,X0_47)
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1573,c_1592])).

cnf(c_2414,plain,
    ( k10_lattice3(sK2,sK3,sK4) = k13_lattice3(sK2,sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1572,c_2143])).

cnf(c_11,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3,plain,
    ( ~ v2_lattice3(X0)
    | ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_25,negated_conjecture,
    ( v2_lattice3(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_646,plain,
    ( ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_25])).

cnf(c_647,plain,
    ( ~ v2_struct_0(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_646])).

cnf(c_80,plain,
    ( ~ v2_lattice3(sK2)
    | ~ v2_struct_0(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_649,plain,
    ( ~ v2_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_647,c_25,c_24,c_80])).

cnf(c_734,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_649])).

cnf(c_735,plain,
    ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ v1_lattice3(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_734])).

cnf(c_739,plain,
    ( ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_735,c_27,c_26,c_24])).

cnf(c_740,plain,
    ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_739])).

cnf(c_1179,plain,
    ( r1_orders_2(sK2,X0_47,k10_lattice3(sK2,X0_47,X1_47))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X0_47,X1_47),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_740])).

cnf(c_1585,plain,
    ( r1_orders_2(sK2,X0_47,k10_lattice3(sK2,X0_47,X1_47)) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k10_lattice3(sK2,X0_47,X1_47),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1179])).

cnf(c_4536,plain,
    ( r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK4)) = iProver_top
    | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2414,c_1585])).

cnf(c_4621,plain,
    ( r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = iProver_top
    | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4536,c_2414])).

cnf(c_12,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK1(X0,X3,X2,X1),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_195,plain,
    ( ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_orders_2(X0,sK1(X0,X3,X2,X1),X1)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_3])).

cnf(c_196,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK1(X0,X3,X2,X1),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(renaming,[status(thm)],[c_195])).

cnf(c_441,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK1(X0,X3,X2,X1),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_196,c_25])).

cnf(c_442,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | ~ r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k11_lattice3(sK2,X2,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_441])).

cnf(c_446,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | ~ r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | k11_lattice3(sK2,X2,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_442,c_27,c_24])).

cnf(c_447,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | ~ r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k11_lattice3(sK2,X2,X1) = X0 ),
    inference(renaming,[status(thm)],[c_446])).

cnf(c_1187,plain,
    ( ~ r1_orders_2(sK2,X0_47,X1_47)
    | ~ r1_orders_2(sK2,X0_47,X2_47)
    | ~ r1_orders_2(sK2,sK1(sK2,X2_47,X1_47,X0_47),X0_47)
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X2_47,u1_struct_0(sK2))
    | k11_lattice3(sK2,X2_47,X1_47) = X0_47 ),
    inference(subtyping,[status(esa)],[c_447])).

cnf(c_2032,plain,
    ( ~ r1_orders_2(sK2,X0_47,k13_lattice3(sK2,sK3,sK4))
    | ~ r1_orders_2(sK2,X0_47,sK3)
    | ~ r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_47),X0_47)
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_47 ),
    inference(instantiation,[status(thm)],[c_1187])).

cnf(c_2048,plain,
    ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_47
    | r1_orders_2(sK2,X0_47,k13_lattice3(sK2,sK3,sK4)) != iProver_top
    | r1_orders_2(sK2,X0_47,sK3) != iProver_top
    | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_47),X0_47) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2032])).

cnf(c_2050,plain,
    ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
    | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),sK3),sK3) != iProver_top
    | r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != iProver_top
    | r1_orders_2(sK2,sK3,sK3) != iProver_top
    | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2048])).

cnf(c_14,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK1(X0,X3,X2,X1),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_183,plain,
    ( ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,sK1(X0,X3,X2,X1),X3)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_3])).

cnf(c_184,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK1(X0,X3,X2,X1),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(renaming,[status(thm)],[c_183])).

cnf(c_507,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK1(X0,X3,X2,X1),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_184,c_25])).

cnf(c_508,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k11_lattice3(sK2,X2,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_507])).

cnf(c_510,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | k11_lattice3(sK2,X2,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_508,c_27,c_24])).

cnf(c_511,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k11_lattice3(sK2,X2,X1) = X0 ),
    inference(renaming,[status(thm)],[c_510])).

cnf(c_1185,plain,
    ( ~ r1_orders_2(sK2,X0_47,X1_47)
    | ~ r1_orders_2(sK2,X0_47,X2_47)
    | r1_orders_2(sK2,sK1(sK2,X2_47,X1_47,X0_47),X2_47)
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X2_47,u1_struct_0(sK2))
    | k11_lattice3(sK2,X2_47,X1_47) = X0_47 ),
    inference(subtyping,[status(esa)],[c_511])).

cnf(c_2034,plain,
    ( ~ r1_orders_2(sK2,X0_47,k13_lattice3(sK2,sK3,sK4))
    | ~ r1_orders_2(sK2,X0_47,sK3)
    | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_47),sK3)
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_47 ),
    inference(instantiation,[status(thm)],[c_1185])).

cnf(c_2040,plain,
    ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_47
    | r1_orders_2(sK2,X0_47,k13_lattice3(sK2,sK3,sK4)) != iProver_top
    | r1_orders_2(sK2,X0_47,sK3) != iProver_top
    | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_47),sK3) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2034])).

cnf(c_2042,plain,
    ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
    | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),sK3),sK3) = iProver_top
    | r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != iProver_top
    | r1_orders_2(sK2,sK3,sK3) != iProver_top
    | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2040])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k13_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1010,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k13_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_24])).

cnf(c_1011,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(k13_lattice3(sK2,X0,X1),u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ v1_lattice3(sK2) ),
    inference(unflattening,[status(thm)],[c_1010])).

cnf(c_1015,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(k13_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1011,c_27,c_26])).

cnf(c_1016,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(k13_lattice3(sK2,X1,X0),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_1015])).

cnf(c_1171,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | m1_subset_1(k13_lattice3(sK2,X1_47,X0_47),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_1016])).

cnf(c_1959,plain,
    ( m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1171])).

cnf(c_1960,plain,
    ( m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1959])).

cnf(c_1197,plain,
    ( X0_47 != X1_47
    | X2_47 != X1_47
    | X2_47 = X0_47 ),
    theory(equality)).

cnf(c_1946,plain,
    ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != X0_47
    | sK3 != X0_47
    | sK3 = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1197])).

cnf(c_1947,plain,
    ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3
    | sK3 = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1946])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_657,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_25])).

cnf(c_658,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k12_lattice3(sK2,X0,X1) = k11_lattice3(sK2,X0,X1) ),
    inference(unflattening,[status(thm)],[c_657])).

cnf(c_662,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k12_lattice3(sK2,X0,X1) = k11_lattice3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_658,c_27,c_24])).

cnf(c_663,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k12_lattice3(sK2,X1,X0) = k11_lattice3(sK2,X1,X0) ),
    inference(renaming,[status(thm)],[c_662])).

cnf(c_1180,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | k12_lattice3(sK2,X1_47,X0_47) = k11_lattice3(sK2,X1_47,X0_47) ),
    inference(subtyping,[status(esa)],[c_663])).

cnf(c_1882,plain,
    ( ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1180])).

cnf(c_1871,plain,
    ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != X0_47
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
    | sK3 != X0_47 ),
    inference(instantiation,[status(thm)],[c_1197])).

cnf(c_1881,plain,
    ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
    | sK3 != k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1871])).

cnf(c_2,plain,
    ( r3_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_28,negated_conjecture,
    ( v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_338,plain,
    ( r3_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_28])).

cnf(c_339,plain,
    ( r3_orders_2(sK2,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_343,plain,
    ( r3_orders_2(sK2,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_339,c_25,c_24,c_80])).

cnf(c_344,plain,
    ( r3_orders_2(sK2,X0,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_343])).

cnf(c_1,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_359,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_28])).

cnf(c_360,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ r3_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_359])).

cnf(c_364,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ r3_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_360,c_25,c_24,c_80])).

cnf(c_365,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ r3_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_364])).

cnf(c_422,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X3,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | X0 != X3
    | X1 != X3
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_344,c_365])).

cnf(c_423,plain,
    ( r1_orders_2(sK2,X0,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_422])).

cnf(c_1188,plain,
    ( r1_orders_2(sK2,X0_47,X0_47)
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_423])).

cnf(c_1192,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1188])).

cnf(c_1214,plain,
    ( m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1192])).

cnf(c_1216,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_1214])).

cnf(c_1193,plain,
    ( r1_orders_2(sK2,X0_47,X0_47)
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_1188])).

cnf(c_1211,plain,
    ( r1_orders_2(sK2,X0_47,X0_47) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1193])).

cnf(c_1213,plain,
    ( r1_orders_2(sK2,sK3,sK3) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_1211])).

cnf(c_1194,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1188])).

cnf(c_1210,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1194])).

cnf(c_21,negated_conjecture,
    ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1191,negated_conjecture,
    ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1196,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_1207,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1196])).

cnf(c_35,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_34,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4621,c_2050,c_2042,c_1960,c_1959,c_1947,c_1882,c_1881,c_1216,c_1213,c_1210,c_1191,c_1207,c_35,c_22,c_34,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:56:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.10/1.06  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.10/1.06  
% 1.10/1.06  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.10/1.06  
% 1.10/1.06  ------  iProver source info
% 1.10/1.06  
% 1.10/1.06  git: date: 2020-06-30 10:37:57 +0100
% 1.10/1.06  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.10/1.06  git: non_committed_changes: false
% 1.10/1.06  git: last_make_outside_of_git: false
% 1.10/1.06  
% 1.10/1.06  ------ 
% 1.10/1.06  
% 1.10/1.06  ------ Input Options
% 1.10/1.06  
% 1.10/1.06  --out_options                           all
% 1.10/1.06  --tptp_safe_out                         true
% 1.10/1.06  --problem_path                          ""
% 1.10/1.06  --include_path                          ""
% 1.10/1.06  --clausifier                            res/vclausify_rel
% 1.10/1.06  --clausifier_options                    --mode clausify
% 1.10/1.06  --stdin                                 false
% 1.10/1.06  --stats_out                             all
% 1.10/1.06  
% 1.10/1.06  ------ General Options
% 1.10/1.06  
% 1.10/1.06  --fof                                   false
% 1.10/1.06  --time_out_real                         305.
% 1.10/1.06  --time_out_virtual                      -1.
% 1.10/1.06  --symbol_type_check                     false
% 1.10/1.06  --clausify_out                          false
% 1.10/1.06  --sig_cnt_out                           false
% 1.10/1.06  --trig_cnt_out                          false
% 1.10/1.06  --trig_cnt_out_tolerance                1.
% 1.10/1.06  --trig_cnt_out_sk_spl                   false
% 1.10/1.06  --abstr_cl_out                          false
% 1.10/1.06  
% 1.10/1.06  ------ Global Options
% 1.10/1.06  
% 1.10/1.06  --schedule                              default
% 1.10/1.06  --add_important_lit                     false
% 1.10/1.06  --prop_solver_per_cl                    1000
% 1.10/1.06  --min_unsat_core                        false
% 1.10/1.06  --soft_assumptions                      false
% 1.10/1.06  --soft_lemma_size                       3
% 1.10/1.06  --prop_impl_unit_size                   0
% 1.10/1.06  --prop_impl_unit                        []
% 1.10/1.06  --share_sel_clauses                     true
% 1.10/1.06  --reset_solvers                         false
% 1.10/1.06  --bc_imp_inh                            [conj_cone]
% 1.10/1.06  --conj_cone_tolerance                   3.
% 1.10/1.06  --extra_neg_conj                        none
% 1.10/1.06  --large_theory_mode                     true
% 1.10/1.06  --prolific_symb_bound                   200
% 1.10/1.06  --lt_threshold                          2000
% 1.10/1.06  --clause_weak_htbl                      true
% 1.10/1.06  --gc_record_bc_elim                     false
% 1.10/1.06  
% 1.10/1.06  ------ Preprocessing Options
% 1.10/1.06  
% 1.10/1.06  --preprocessing_flag                    true
% 1.10/1.06  --time_out_prep_mult                    0.1
% 1.10/1.06  --splitting_mode                        input
% 1.10/1.06  --splitting_grd                         true
% 1.10/1.06  --splitting_cvd                         false
% 1.10/1.06  --splitting_cvd_svl                     false
% 1.10/1.06  --splitting_nvd                         32
% 1.10/1.06  --sub_typing                            true
% 1.10/1.06  --prep_gs_sim                           true
% 1.10/1.06  --prep_unflatten                        true
% 1.10/1.06  --prep_res_sim                          true
% 1.10/1.06  --prep_upred                            true
% 1.10/1.06  --prep_sem_filter                       exhaustive
% 1.10/1.06  --prep_sem_filter_out                   false
% 1.10/1.06  --pred_elim                             true
% 1.10/1.06  --res_sim_input                         true
% 1.10/1.06  --eq_ax_congr_red                       true
% 1.10/1.06  --pure_diseq_elim                       true
% 1.10/1.06  --brand_transform                       false
% 1.10/1.06  --non_eq_to_eq                          false
% 1.10/1.06  --prep_def_merge                        true
% 1.10/1.06  --prep_def_merge_prop_impl              false
% 1.10/1.06  --prep_def_merge_mbd                    true
% 1.10/1.06  --prep_def_merge_tr_red                 false
% 1.10/1.06  --prep_def_merge_tr_cl                  false
% 1.10/1.06  --smt_preprocessing                     true
% 1.10/1.06  --smt_ac_axioms                         fast
% 1.10/1.06  --preprocessed_out                      false
% 1.10/1.06  --preprocessed_stats                    false
% 1.10/1.06  
% 1.10/1.06  ------ Abstraction refinement Options
% 1.10/1.06  
% 1.10/1.06  --abstr_ref                             []
% 1.10/1.06  --abstr_ref_prep                        false
% 1.10/1.06  --abstr_ref_until_sat                   false
% 1.10/1.06  --abstr_ref_sig_restrict                funpre
% 1.10/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 1.10/1.06  --abstr_ref_under                       []
% 1.10/1.06  
% 1.10/1.06  ------ SAT Options
% 1.10/1.06  
% 1.10/1.06  --sat_mode                              false
% 1.10/1.06  --sat_fm_restart_options                ""
% 1.10/1.06  --sat_gr_def                            false
% 1.10/1.06  --sat_epr_types                         true
% 1.10/1.06  --sat_non_cyclic_types                  false
% 1.10/1.06  --sat_finite_models                     false
% 1.10/1.06  --sat_fm_lemmas                         false
% 1.10/1.06  --sat_fm_prep                           false
% 1.10/1.06  --sat_fm_uc_incr                        true
% 1.10/1.06  --sat_out_model                         small
% 1.10/1.06  --sat_out_clauses                       false
% 1.10/1.06  
% 1.10/1.06  ------ QBF Options
% 1.10/1.06  
% 1.10/1.06  --qbf_mode                              false
% 1.10/1.06  --qbf_elim_univ                         false
% 1.10/1.06  --qbf_dom_inst                          none
% 1.10/1.06  --qbf_dom_pre_inst                      false
% 1.10/1.06  --qbf_sk_in                             false
% 1.10/1.06  --qbf_pred_elim                         true
% 1.10/1.06  --qbf_split                             512
% 1.10/1.06  
% 1.10/1.06  ------ BMC1 Options
% 1.10/1.06  
% 1.10/1.06  --bmc1_incremental                      false
% 1.10/1.06  --bmc1_axioms                           reachable_all
% 1.10/1.06  --bmc1_min_bound                        0
% 1.10/1.06  --bmc1_max_bound                        -1
% 1.10/1.06  --bmc1_max_bound_default                -1
% 1.10/1.06  --bmc1_symbol_reachability              true
% 1.10/1.06  --bmc1_property_lemmas                  false
% 1.10/1.06  --bmc1_k_induction                      false
% 1.10/1.06  --bmc1_non_equiv_states                 false
% 1.10/1.06  --bmc1_deadlock                         false
% 1.10/1.06  --bmc1_ucm                              false
% 1.10/1.06  --bmc1_add_unsat_core                   none
% 1.10/1.06  --bmc1_unsat_core_children              false
% 1.10/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 1.10/1.06  --bmc1_out_stat                         full
% 1.10/1.06  --bmc1_ground_init                      false
% 1.10/1.06  --bmc1_pre_inst_next_state              false
% 1.10/1.06  --bmc1_pre_inst_state                   false
% 1.10/1.06  --bmc1_pre_inst_reach_state             false
% 1.10/1.06  --bmc1_out_unsat_core                   false
% 1.10/1.06  --bmc1_aig_witness_out                  false
% 1.10/1.06  --bmc1_verbose                          false
% 1.10/1.06  --bmc1_dump_clauses_tptp                false
% 1.10/1.06  --bmc1_dump_unsat_core_tptp             false
% 1.10/1.06  --bmc1_dump_file                        -
% 1.10/1.06  --bmc1_ucm_expand_uc_limit              128
% 1.10/1.06  --bmc1_ucm_n_expand_iterations          6
% 1.10/1.06  --bmc1_ucm_extend_mode                  1
% 1.10/1.06  --bmc1_ucm_init_mode                    2
% 1.10/1.06  --bmc1_ucm_cone_mode                    none
% 1.10/1.06  --bmc1_ucm_reduced_relation_type        0
% 1.10/1.06  --bmc1_ucm_relax_model                  4
% 1.10/1.06  --bmc1_ucm_full_tr_after_sat            true
% 1.10/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 1.10/1.06  --bmc1_ucm_layered_model                none
% 1.10/1.06  --bmc1_ucm_max_lemma_size               10
% 1.10/1.06  
% 1.10/1.06  ------ AIG Options
% 1.10/1.06  
% 1.10/1.06  --aig_mode                              false
% 1.10/1.06  
% 1.10/1.06  ------ Instantiation Options
% 1.10/1.06  
% 1.10/1.06  --instantiation_flag                    true
% 1.10/1.06  --inst_sos_flag                         false
% 1.10/1.06  --inst_sos_phase                        true
% 1.10/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.10/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.10/1.06  --inst_lit_sel_side                     num_symb
% 1.10/1.06  --inst_solver_per_active                1400
% 1.10/1.06  --inst_solver_calls_frac                1.
% 1.10/1.06  --inst_passive_queue_type               priority_queues
% 1.10/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.10/1.06  --inst_passive_queues_freq              [25;2]
% 1.10/1.06  --inst_dismatching                      true
% 1.10/1.06  --inst_eager_unprocessed_to_passive     true
% 1.10/1.06  --inst_prop_sim_given                   true
% 1.10/1.06  --inst_prop_sim_new                     false
% 1.10/1.06  --inst_subs_new                         false
% 1.10/1.06  --inst_eq_res_simp                      false
% 1.10/1.06  --inst_subs_given                       false
% 1.10/1.06  --inst_orphan_elimination               true
% 1.10/1.06  --inst_learning_loop_flag               true
% 1.10/1.06  --inst_learning_start                   3000
% 1.10/1.06  --inst_learning_factor                  2
% 1.10/1.06  --inst_start_prop_sim_after_learn       3
% 1.10/1.06  --inst_sel_renew                        solver
% 1.10/1.06  --inst_lit_activity_flag                true
% 1.10/1.06  --inst_restr_to_given                   false
% 1.10/1.06  --inst_activity_threshold               500
% 1.10/1.06  --inst_out_proof                        true
% 1.10/1.06  
% 1.10/1.06  ------ Resolution Options
% 1.10/1.06  
% 1.10/1.06  --resolution_flag                       true
% 1.10/1.06  --res_lit_sel                           adaptive
% 1.10/1.06  --res_lit_sel_side                      none
% 1.10/1.06  --res_ordering                          kbo
% 1.10/1.06  --res_to_prop_solver                    active
% 1.10/1.06  --res_prop_simpl_new                    false
% 1.10/1.06  --res_prop_simpl_given                  true
% 1.10/1.06  --res_passive_queue_type                priority_queues
% 1.10/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.10/1.06  --res_passive_queues_freq               [15;5]
% 1.10/1.06  --res_forward_subs                      full
% 1.10/1.06  --res_backward_subs                     full
% 1.10/1.06  --res_forward_subs_resolution           true
% 1.10/1.06  --res_backward_subs_resolution          true
% 1.10/1.06  --res_orphan_elimination                true
% 1.10/1.06  --res_time_limit                        2.
% 1.10/1.06  --res_out_proof                         true
% 1.10/1.06  
% 1.10/1.06  ------ Superposition Options
% 1.10/1.06  
% 1.10/1.06  --superposition_flag                    true
% 1.10/1.06  --sup_passive_queue_type                priority_queues
% 1.10/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.10/1.06  --sup_passive_queues_freq               [8;1;4]
% 1.10/1.06  --demod_completeness_check              fast
% 1.10/1.06  --demod_use_ground                      true
% 1.10/1.06  --sup_to_prop_solver                    passive
% 1.10/1.06  --sup_prop_simpl_new                    true
% 1.10/1.06  --sup_prop_simpl_given                  true
% 1.10/1.06  --sup_fun_splitting                     false
% 1.10/1.06  --sup_smt_interval                      50000
% 1.10/1.06  
% 1.10/1.06  ------ Superposition Simplification Setup
% 1.10/1.06  
% 1.10/1.06  --sup_indices_passive                   []
% 1.10/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.10/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.10/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.10/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 1.10/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.10/1.06  --sup_full_bw                           [BwDemod]
% 1.10/1.06  --sup_immed_triv                        [TrivRules]
% 1.10/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.10/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.10/1.06  --sup_immed_bw_main                     []
% 1.10/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.10/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 1.10/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.10/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.10/1.06  
% 1.10/1.06  ------ Combination Options
% 1.10/1.06  
% 1.10/1.06  --comb_res_mult                         3
% 1.10/1.06  --comb_sup_mult                         2
% 1.10/1.06  --comb_inst_mult                        10
% 1.10/1.06  
% 1.10/1.06  ------ Debug Options
% 1.10/1.06  
% 1.10/1.06  --dbg_backtrace                         false
% 1.10/1.06  --dbg_dump_prop_clauses                 false
% 1.10/1.06  --dbg_dump_prop_clauses_file            -
% 1.10/1.06  --dbg_out_stat                          false
% 1.10/1.06  ------ Parsing...
% 1.10/1.06  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.10/1.06  
% 1.10/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 1.10/1.06  
% 1.10/1.06  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.10/1.06  
% 1.10/1.06  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.10/1.06  ------ Proving...
% 1.10/1.06  ------ Problem Properties 
% 1.10/1.06  
% 1.10/1.06  
% 1.10/1.06  clauses                                 23
% 1.10/1.06  conjectures                             3
% 1.10/1.06  EPR                                     1
% 1.10/1.06  Horn                                    16
% 1.10/1.06  unary                                   3
% 1.10/1.06  binary                                  2
% 1.10/1.06  lits                                    105
% 1.10/1.06  lits eq                                 11
% 1.10/1.06  fd_pure                                 0
% 1.10/1.06  fd_pseudo                               0
% 1.10/1.06  fd_cond                                 0
% 1.10/1.06  fd_pseudo_cond                          8
% 1.10/1.06  AC symbols                              0
% 1.10/1.06  
% 1.10/1.06  ------ Schedule dynamic 5 is on 
% 1.10/1.06  
% 1.10/1.06  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.10/1.06  
% 1.10/1.06  
% 1.10/1.06  ------ 
% 1.10/1.06  Current options:
% 1.10/1.06  ------ 
% 1.10/1.06  
% 1.10/1.06  ------ Input Options
% 1.10/1.06  
% 1.10/1.06  --out_options                           all
% 1.10/1.06  --tptp_safe_out                         true
% 1.10/1.06  --problem_path                          ""
% 1.10/1.06  --include_path                          ""
% 1.10/1.06  --clausifier                            res/vclausify_rel
% 1.10/1.06  --clausifier_options                    --mode clausify
% 1.10/1.06  --stdin                                 false
% 1.10/1.06  --stats_out                             all
% 1.10/1.06  
% 1.10/1.06  ------ General Options
% 1.10/1.06  
% 1.10/1.06  --fof                                   false
% 1.10/1.06  --time_out_real                         305.
% 1.10/1.06  --time_out_virtual                      -1.
% 1.10/1.06  --symbol_type_check                     false
% 1.10/1.06  --clausify_out                          false
% 1.10/1.06  --sig_cnt_out                           false
% 1.10/1.06  --trig_cnt_out                          false
% 1.10/1.06  --trig_cnt_out_tolerance                1.
% 1.10/1.06  --trig_cnt_out_sk_spl                   false
% 1.10/1.06  --abstr_cl_out                          false
% 1.10/1.06  
% 1.10/1.06  ------ Global Options
% 1.10/1.06  
% 1.10/1.06  --schedule                              default
% 1.10/1.06  --add_important_lit                     false
% 1.10/1.06  --prop_solver_per_cl                    1000
% 1.10/1.06  --min_unsat_core                        false
% 1.10/1.06  --soft_assumptions                      false
% 1.10/1.06  --soft_lemma_size                       3
% 1.10/1.06  --prop_impl_unit_size                   0
% 1.10/1.06  --prop_impl_unit                        []
% 1.10/1.06  --share_sel_clauses                     true
% 1.10/1.06  --reset_solvers                         false
% 1.10/1.06  --bc_imp_inh                            [conj_cone]
% 1.10/1.06  --conj_cone_tolerance                   3.
% 1.10/1.06  --extra_neg_conj                        none
% 1.10/1.06  --large_theory_mode                     true
% 1.10/1.06  --prolific_symb_bound                   200
% 1.10/1.06  --lt_threshold                          2000
% 1.10/1.06  --clause_weak_htbl                      true
% 1.10/1.06  --gc_record_bc_elim                     false
% 1.10/1.06  
% 1.10/1.06  ------ Preprocessing Options
% 1.10/1.06  
% 1.10/1.06  --preprocessing_flag                    true
% 1.10/1.06  --time_out_prep_mult                    0.1
% 1.10/1.06  --splitting_mode                        input
% 1.10/1.06  --splitting_grd                         true
% 1.10/1.06  --splitting_cvd                         false
% 1.10/1.06  --splitting_cvd_svl                     false
% 1.10/1.06  --splitting_nvd                         32
% 1.10/1.06  --sub_typing                            true
% 1.10/1.06  --prep_gs_sim                           true
% 1.10/1.06  --prep_unflatten                        true
% 1.10/1.06  --prep_res_sim                          true
% 1.10/1.06  --prep_upred                            true
% 1.10/1.06  --prep_sem_filter                       exhaustive
% 1.10/1.06  --prep_sem_filter_out                   false
% 1.10/1.06  --pred_elim                             true
% 1.10/1.06  --res_sim_input                         true
% 1.10/1.06  --eq_ax_congr_red                       true
% 1.10/1.06  --pure_diseq_elim                       true
% 1.10/1.06  --brand_transform                       false
% 1.10/1.06  --non_eq_to_eq                          false
% 1.10/1.06  --prep_def_merge                        true
% 1.10/1.06  --prep_def_merge_prop_impl              false
% 1.10/1.06  --prep_def_merge_mbd                    true
% 1.10/1.06  --prep_def_merge_tr_red                 false
% 1.10/1.06  --prep_def_merge_tr_cl                  false
% 1.10/1.06  --smt_preprocessing                     true
% 1.10/1.06  --smt_ac_axioms                         fast
% 1.10/1.06  --preprocessed_out                      false
% 1.10/1.06  --preprocessed_stats                    false
% 1.10/1.06  
% 1.10/1.06  ------ Abstraction refinement Options
% 1.10/1.06  
% 1.10/1.06  --abstr_ref                             []
% 1.10/1.06  --abstr_ref_prep                        false
% 1.10/1.06  --abstr_ref_until_sat                   false
% 1.10/1.06  --abstr_ref_sig_restrict                funpre
% 1.10/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 1.10/1.06  --abstr_ref_under                       []
% 1.10/1.06  
% 1.10/1.06  ------ SAT Options
% 1.10/1.06  
% 1.10/1.06  --sat_mode                              false
% 1.10/1.06  --sat_fm_restart_options                ""
% 1.10/1.06  --sat_gr_def                            false
% 1.10/1.06  --sat_epr_types                         true
% 1.10/1.06  --sat_non_cyclic_types                  false
% 1.10/1.06  --sat_finite_models                     false
% 1.10/1.06  --sat_fm_lemmas                         false
% 1.10/1.06  --sat_fm_prep                           false
% 1.10/1.06  --sat_fm_uc_incr                        true
% 1.10/1.06  --sat_out_model                         small
% 1.10/1.06  --sat_out_clauses                       false
% 1.10/1.06  
% 1.10/1.06  ------ QBF Options
% 1.10/1.06  
% 1.10/1.06  --qbf_mode                              false
% 1.10/1.06  --qbf_elim_univ                         false
% 1.10/1.06  --qbf_dom_inst                          none
% 1.10/1.06  --qbf_dom_pre_inst                      false
% 1.10/1.06  --qbf_sk_in                             false
% 1.10/1.06  --qbf_pred_elim                         true
% 1.10/1.06  --qbf_split                             512
% 1.10/1.06  
% 1.10/1.06  ------ BMC1 Options
% 1.10/1.06  
% 1.10/1.06  --bmc1_incremental                      false
% 1.10/1.06  --bmc1_axioms                           reachable_all
% 1.10/1.06  --bmc1_min_bound                        0
% 1.10/1.06  --bmc1_max_bound                        -1
% 1.10/1.06  --bmc1_max_bound_default                -1
% 1.10/1.06  --bmc1_symbol_reachability              true
% 1.10/1.06  --bmc1_property_lemmas                  false
% 1.10/1.06  --bmc1_k_induction                      false
% 1.10/1.06  --bmc1_non_equiv_states                 false
% 1.10/1.06  --bmc1_deadlock                         false
% 1.10/1.06  --bmc1_ucm                              false
% 1.10/1.06  --bmc1_add_unsat_core                   none
% 1.10/1.06  --bmc1_unsat_core_children              false
% 1.10/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 1.10/1.06  --bmc1_out_stat                         full
% 1.10/1.06  --bmc1_ground_init                      false
% 1.10/1.06  --bmc1_pre_inst_next_state              false
% 1.10/1.06  --bmc1_pre_inst_state                   false
% 1.10/1.06  --bmc1_pre_inst_reach_state             false
% 1.10/1.06  --bmc1_out_unsat_core                   false
% 1.10/1.06  --bmc1_aig_witness_out                  false
% 1.10/1.06  --bmc1_verbose                          false
% 1.10/1.06  --bmc1_dump_clauses_tptp                false
% 1.10/1.06  --bmc1_dump_unsat_core_tptp             false
% 1.10/1.06  --bmc1_dump_file                        -
% 1.10/1.06  --bmc1_ucm_expand_uc_limit              128
% 1.10/1.06  --bmc1_ucm_n_expand_iterations          6
% 1.10/1.06  --bmc1_ucm_extend_mode                  1
% 1.10/1.06  --bmc1_ucm_init_mode                    2
% 1.10/1.06  --bmc1_ucm_cone_mode                    none
% 1.10/1.06  --bmc1_ucm_reduced_relation_type        0
% 1.10/1.06  --bmc1_ucm_relax_model                  4
% 1.10/1.06  --bmc1_ucm_full_tr_after_sat            true
% 1.10/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 1.10/1.06  --bmc1_ucm_layered_model                none
% 1.10/1.06  --bmc1_ucm_max_lemma_size               10
% 1.10/1.06  
% 1.10/1.06  ------ AIG Options
% 1.10/1.06  
% 1.10/1.06  --aig_mode                              false
% 1.10/1.06  
% 1.10/1.06  ------ Instantiation Options
% 1.10/1.06  
% 1.10/1.06  --instantiation_flag                    true
% 1.10/1.06  --inst_sos_flag                         false
% 1.10/1.06  --inst_sos_phase                        true
% 1.10/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.10/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.10/1.06  --inst_lit_sel_side                     none
% 1.10/1.06  --inst_solver_per_active                1400
% 1.10/1.06  --inst_solver_calls_frac                1.
% 1.10/1.06  --inst_passive_queue_type               priority_queues
% 1.10/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.10/1.06  --inst_passive_queues_freq              [25;2]
% 1.10/1.06  --inst_dismatching                      true
% 1.10/1.06  --inst_eager_unprocessed_to_passive     true
% 1.10/1.06  --inst_prop_sim_given                   true
% 1.10/1.06  --inst_prop_sim_new                     false
% 1.10/1.06  --inst_subs_new                         false
% 1.10/1.06  --inst_eq_res_simp                      false
% 1.10/1.06  --inst_subs_given                       false
% 1.10/1.06  --inst_orphan_elimination               true
% 1.10/1.06  --inst_learning_loop_flag               true
% 1.10/1.06  --inst_learning_start                   3000
% 1.10/1.06  --inst_learning_factor                  2
% 1.10/1.06  --inst_start_prop_sim_after_learn       3
% 1.10/1.06  --inst_sel_renew                        solver
% 1.10/1.06  --inst_lit_activity_flag                true
% 1.10/1.06  --inst_restr_to_given                   false
% 1.10/1.06  --inst_activity_threshold               500
% 1.10/1.06  --inst_out_proof                        true
% 1.10/1.06  
% 1.10/1.06  ------ Resolution Options
% 1.10/1.06  
% 1.10/1.06  --resolution_flag                       false
% 1.10/1.06  --res_lit_sel                           adaptive
% 1.10/1.06  --res_lit_sel_side                      none
% 1.10/1.06  --res_ordering                          kbo
% 1.10/1.06  --res_to_prop_solver                    active
% 1.10/1.06  --res_prop_simpl_new                    false
% 1.10/1.06  --res_prop_simpl_given                  true
% 1.10/1.06  --res_passive_queue_type                priority_queues
% 1.10/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.10/1.06  --res_passive_queues_freq               [15;5]
% 1.10/1.06  --res_forward_subs                      full
% 1.10/1.06  --res_backward_subs                     full
% 1.10/1.06  --res_forward_subs_resolution           true
% 1.10/1.06  --res_backward_subs_resolution          true
% 1.10/1.06  --res_orphan_elimination                true
% 1.10/1.06  --res_time_limit                        2.
% 1.10/1.06  --res_out_proof                         true
% 1.10/1.06  
% 1.10/1.06  ------ Superposition Options
% 1.10/1.06  
% 1.10/1.06  --superposition_flag                    true
% 1.10/1.06  --sup_passive_queue_type                priority_queues
% 1.10/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.10/1.06  --sup_passive_queues_freq               [8;1;4]
% 1.10/1.06  --demod_completeness_check              fast
% 1.10/1.06  --demod_use_ground                      true
% 1.10/1.06  --sup_to_prop_solver                    passive
% 1.10/1.06  --sup_prop_simpl_new                    true
% 1.10/1.06  --sup_prop_simpl_given                  true
% 1.10/1.06  --sup_fun_splitting                     false
% 1.10/1.06  --sup_smt_interval                      50000
% 1.10/1.06  
% 1.10/1.06  ------ Superposition Simplification Setup
% 1.10/1.06  
% 1.10/1.06  --sup_indices_passive                   []
% 1.10/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.10/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.10/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.10/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 1.10/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.10/1.06  --sup_full_bw                           [BwDemod]
% 1.10/1.06  --sup_immed_triv                        [TrivRules]
% 1.10/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.10/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.10/1.06  --sup_immed_bw_main                     []
% 1.10/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.10/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 1.10/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.10/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.10/1.06  
% 1.10/1.06  ------ Combination Options
% 1.10/1.06  
% 1.10/1.06  --comb_res_mult                         3
% 1.10/1.06  --comb_sup_mult                         2
% 1.10/1.06  --comb_inst_mult                        10
% 1.10/1.06  
% 1.10/1.06  ------ Debug Options
% 1.10/1.06  
% 1.10/1.06  --dbg_backtrace                         false
% 1.10/1.06  --dbg_dump_prop_clauses                 false
% 1.10/1.06  --dbg_dump_prop_clauses_file            -
% 1.10/1.06  --dbg_out_stat                          false
% 1.10/1.06  
% 1.10/1.06  
% 1.10/1.06  
% 1.10/1.06  
% 1.10/1.06  ------ Proving...
% 1.10/1.06  
% 1.10/1.06  
% 1.10/1.06  % SZS status Theorem for theBenchmark.p
% 1.10/1.06  
% 1.10/1.06  % SZS output start CNFRefutation for theBenchmark.p
% 1.10/1.06  
% 1.10/1.06  fof(f9,conjecture,(
% 1.10/1.06    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1)))),
% 1.10/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.10/1.06  
% 1.10/1.06  fof(f10,negated_conjecture,(
% 1.10/1.06    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1)))),
% 1.10/1.06    inference(negated_conjecture,[],[f9])).
% 1.10/1.06  
% 1.10/1.06  fof(f27,plain,(
% 1.10/1.06    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)))),
% 1.10/1.06    inference(ennf_transformation,[],[f10])).
% 1.10/1.06  
% 1.10/1.06  fof(f28,plain,(
% 1.10/1.06    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 1.10/1.06    inference(flattening,[],[f27])).
% 1.10/1.06  
% 1.10/1.06  fof(f42,plain,(
% 1.10/1.06    ( ! [X0,X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) => (k12_lattice3(X0,X1,k13_lattice3(X0,X1,sK4)) != X1 & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 1.10/1.06    introduced(choice_axiom,[])).
% 1.10/1.06  
% 1.10/1.06  fof(f41,plain,(
% 1.10/1.06    ( ! [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k12_lattice3(X0,sK3,k13_lattice3(X0,sK3,X2)) != sK3 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 1.10/1.06    introduced(choice_axiom,[])).
% 1.10/1.06  
% 1.10/1.06  fof(f40,plain,(
% 1.10/1.06    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => (? [X1] : (? [X2] : (k12_lattice3(sK2,X1,k13_lattice3(sK2,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_orders_2(sK2) & v2_lattice3(sK2) & v1_lattice3(sK2) & v5_orders_2(sK2) & v3_orders_2(sK2))),
% 1.10/1.06    introduced(choice_axiom,[])).
% 1.10/1.06  
% 1.10/1.06  fof(f43,plain,(
% 1.10/1.06    ((k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 & m1_subset_1(sK4,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_orders_2(sK2) & v2_lattice3(sK2) & v1_lattice3(sK2) & v5_orders_2(sK2) & v3_orders_2(sK2)),
% 1.10/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f28,f42,f41,f40])).
% 1.10/1.06  
% 1.10/1.06  fof(f71,plain,(
% 1.10/1.06    m1_subset_1(sK4,u1_struct_0(sK2))),
% 1.10/1.06    inference(cnf_transformation,[],[f43])).
% 1.10/1.06  
% 1.10/1.06  fof(f70,plain,(
% 1.10/1.06    m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.10/1.06    inference(cnf_transformation,[],[f43])).
% 1.10/1.06  
% 1.10/1.06  fof(f8,axiom,(
% 1.10/1.06    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2))),
% 1.10/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.10/1.06  
% 1.10/1.06  fof(f25,plain,(
% 1.10/1.06    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 1.10/1.06    inference(ennf_transformation,[],[f8])).
% 1.10/1.06  
% 1.10/1.06  fof(f26,plain,(
% 1.10/1.06    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 1.10/1.06    inference(flattening,[],[f25])).
% 1.10/1.06  
% 1.10/1.06  fof(f64,plain,(
% 1.10/1.06    ( ! [X2,X0,X1] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 1.10/1.06    inference(cnf_transformation,[],[f26])).
% 1.10/1.06  
% 1.10/1.06  fof(f69,plain,(
% 1.10/1.06    l1_orders_2(sK2)),
% 1.10/1.06    inference(cnf_transformation,[],[f43])).
% 1.10/1.06  
% 1.10/1.06  fof(f66,plain,(
% 1.10/1.06    v5_orders_2(sK2)),
% 1.10/1.06    inference(cnf_transformation,[],[f43])).
% 1.10/1.06  
% 1.10/1.06  fof(f67,plain,(
% 1.10/1.06    v1_lattice3(sK2)),
% 1.10/1.06    inference(cnf_transformation,[],[f43])).
% 1.10/1.06  
% 1.10/1.06  fof(f5,axiom,(
% 1.10/1.06    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 1.10/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.10/1.06  
% 1.10/1.06  fof(f19,plain,(
% 1.10/1.06    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 1.10/1.06    inference(ennf_transformation,[],[f5])).
% 1.10/1.06  
% 1.10/1.06  fof(f20,plain,(
% 1.10/1.06    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.10/1.06    inference(flattening,[],[f19])).
% 1.10/1.06  
% 1.10/1.06  fof(f30,plain,(
% 1.10/1.06    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3))) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.10/1.06    inference(nnf_transformation,[],[f20])).
% 1.10/1.06  
% 1.10/1.06  fof(f31,plain,(
% 1.10/1.06    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.10/1.06    inference(flattening,[],[f30])).
% 1.10/1.06  
% 1.10/1.06  fof(f32,plain,(
% 1.10/1.06    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.10/1.06    inference(rectify,[],[f31])).
% 1.10/1.06  
% 1.10/1.06  fof(f33,plain,(
% 1.10/1.06    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,X3,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))))),
% 1.10/1.06    introduced(choice_axiom,[])).
% 1.10/1.06  
% 1.10/1.06  fof(f34,plain,(
% 1.10/1.06    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,X3,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.10/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 1.10/1.06  
% 1.10/1.06  fof(f49,plain,(
% 1.10/1.06    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X1,X3) | k10_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.10/1.06    inference(cnf_transformation,[],[f34])).
% 1.10/1.06  
% 1.10/1.06  fof(f75,plain,(
% 1.10/1.06    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.10/1.06    inference(equality_resolution,[],[f49])).
% 1.10/1.06  
% 1.10/1.06  fof(f3,axiom,(
% 1.10/1.06    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 1.10/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.10/1.06  
% 1.10/1.06  fof(f15,plain,(
% 1.10/1.06    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 1.10/1.06    inference(ennf_transformation,[],[f3])).
% 1.10/1.06  
% 1.10/1.06  fof(f16,plain,(
% 1.10/1.06    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 1.10/1.06    inference(flattening,[],[f15])).
% 1.10/1.06  
% 1.10/1.06  fof(f47,plain,(
% 1.10/1.06    ( ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0)) )),
% 1.10/1.06    inference(cnf_transformation,[],[f16])).
% 1.10/1.06  
% 1.10/1.06  fof(f68,plain,(
% 1.10/1.06    v2_lattice3(sK2)),
% 1.10/1.06    inference(cnf_transformation,[],[f43])).
% 1.10/1.06  
% 1.10/1.06  fof(f6,axiom,(
% 1.10/1.06    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 1.10/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.10/1.06  
% 1.10/1.06  fof(f21,plain,(
% 1.10/1.06    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 1.10/1.06    inference(ennf_transformation,[],[f6])).
% 1.10/1.06  
% 1.10/1.06  fof(f22,plain,(
% 1.10/1.06    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.10/1.06    inference(flattening,[],[f21])).
% 1.10/1.06  
% 1.10/1.06  fof(f35,plain,(
% 1.10/1.06    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.10/1.06    inference(nnf_transformation,[],[f22])).
% 1.10/1.06  
% 1.10/1.06  fof(f36,plain,(
% 1.10/1.06    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.10/1.06    inference(flattening,[],[f35])).
% 1.10/1.06  
% 1.10/1.06  fof(f37,plain,(
% 1.10/1.06    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.10/1.06    inference(rectify,[],[f36])).
% 1.10/1.06  
% 1.10/1.06  fof(f38,plain,(
% 1.10/1.06    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK1(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X1) & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0))))),
% 1.10/1.06    introduced(choice_axiom,[])).
% 1.10/1.06  
% 1.10/1.06  fof(f39,plain,(
% 1.10/1.06    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,sK1(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X1) & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.10/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).
% 1.10/1.06  
% 1.10/1.06  fof(f62,plain,(
% 1.10/1.06    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,sK1(X0,X1,X2,X3),X3) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.10/1.06    inference(cnf_transformation,[],[f39])).
% 1.10/1.06  
% 1.10/1.06  fof(f60,plain,(
% 1.10/1.06    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | r1_orders_2(X0,sK1(X0,X1,X2,X3),X1) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.10/1.06    inference(cnf_transformation,[],[f39])).
% 1.10/1.06  
% 1.10/1.06  fof(f4,axiom,(
% 1.10/1.06    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 1.10/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.10/1.06  
% 1.10/1.06  fof(f17,plain,(
% 1.10/1.06    ! [X0,X1,X2] : (m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 1.10/1.06    inference(ennf_transformation,[],[f4])).
% 1.10/1.06  
% 1.10/1.06  fof(f18,plain,(
% 1.10/1.06    ! [X0,X1,X2] : (m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 1.10/1.06    inference(flattening,[],[f17])).
% 1.10/1.06  
% 1.10/1.06  fof(f48,plain,(
% 1.10/1.06    ( ! [X2,X0,X1] : (m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 1.10/1.06    inference(cnf_transformation,[],[f18])).
% 1.10/1.06  
% 1.10/1.06  fof(f7,axiom,(
% 1.10/1.06    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2))),
% 1.10/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.10/1.06  
% 1.10/1.06  fof(f23,plain,(
% 1.10/1.06    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 1.10/1.06    inference(ennf_transformation,[],[f7])).
% 1.10/1.06  
% 1.10/1.06  fof(f24,plain,(
% 1.10/1.06    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 1.10/1.06    inference(flattening,[],[f23])).
% 1.10/1.06  
% 1.10/1.06  fof(f63,plain,(
% 1.10/1.06    ( ! [X2,X0,X1] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 1.10/1.06    inference(cnf_transformation,[],[f24])).
% 1.10/1.06  
% 1.10/1.06  fof(f2,axiom,(
% 1.10/1.06    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => r3_orders_2(X0,X1,X1))),
% 1.10/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.10/1.06  
% 1.10/1.06  fof(f13,plain,(
% 1.10/1.06    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.10/1.06    inference(ennf_transformation,[],[f2])).
% 1.10/1.06  
% 1.10/1.06  fof(f14,plain,(
% 1.10/1.06    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.10/1.06    inference(flattening,[],[f13])).
% 1.10/1.06  
% 1.10/1.06  fof(f46,plain,(
% 1.10/1.06    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.10/1.06    inference(cnf_transformation,[],[f14])).
% 1.10/1.06  
% 1.10/1.06  fof(f65,plain,(
% 1.10/1.06    v3_orders_2(sK2)),
% 1.10/1.06    inference(cnf_transformation,[],[f43])).
% 1.10/1.06  
% 1.10/1.06  fof(f1,axiom,(
% 1.10/1.06    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 1.10/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.10/1.06  
% 1.10/1.06  fof(f11,plain,(
% 1.10/1.06    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.10/1.06    inference(ennf_transformation,[],[f1])).
% 1.10/1.06  
% 1.10/1.06  fof(f12,plain,(
% 1.10/1.06    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.10/1.06    inference(flattening,[],[f11])).
% 1.10/1.06  
% 1.10/1.06  fof(f29,plain,(
% 1.10/1.06    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.10/1.06    inference(nnf_transformation,[],[f12])).
% 1.10/1.06  
% 1.10/1.06  fof(f44,plain,(
% 1.10/1.06    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.10/1.06    inference(cnf_transformation,[],[f29])).
% 1.10/1.06  
% 1.10/1.06  fof(f72,plain,(
% 1.10/1.06    k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3),
% 1.10/1.06    inference(cnf_transformation,[],[f43])).
% 1.10/1.06  
% 1.10/1.06  cnf(c_22,negated_conjecture,
% 1.10/1.06      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 1.10/1.06      inference(cnf_transformation,[],[f71]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_1190,negated_conjecture,
% 1.10/1.06      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 1.10/1.06      inference(subtyping,[status(esa)],[c_22]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_1572,plain,
% 1.10/1.06      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 1.10/1.06      inference(predicate_to_equality,[status(thm)],[c_1190]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_23,negated_conjecture,
% 1.10/1.06      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 1.10/1.06      inference(cnf_transformation,[],[f70]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_1189,negated_conjecture,
% 1.10/1.06      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 1.10/1.06      inference(subtyping,[status(esa)],[c_23]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_1573,plain,
% 1.10/1.06      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 1.10/1.06      inference(predicate_to_equality,[status(thm)],[c_1189]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_20,plain,
% 1.10/1.06      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.10/1.06      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.10/1.06      | ~ v5_orders_2(X1)
% 1.10/1.06      | ~ v1_lattice3(X1)
% 1.10/1.06      | ~ l1_orders_2(X1)
% 1.10/1.06      | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0) ),
% 1.10/1.06      inference(cnf_transformation,[],[f64]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_24,negated_conjecture,
% 1.10/1.06      ( l1_orders_2(sK2) ),
% 1.10/1.06      inference(cnf_transformation,[],[f69]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_989,plain,
% 1.10/1.06      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.10/1.06      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.10/1.06      | ~ v5_orders_2(X1)
% 1.10/1.06      | ~ v1_lattice3(X1)
% 1.10/1.06      | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0)
% 1.10/1.06      | sK2 != X1 ),
% 1.10/1.06      inference(resolution_lifted,[status(thm)],[c_20,c_24]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_990,plain,
% 1.10/1.06      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.10/1.06      | ~ v5_orders_2(sK2)
% 1.10/1.06      | ~ v1_lattice3(sK2)
% 1.10/1.06      | k10_lattice3(sK2,X0,X1) = k13_lattice3(sK2,X0,X1) ),
% 1.10/1.06      inference(unflattening,[status(thm)],[c_989]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_27,negated_conjecture,
% 1.10/1.06      ( v5_orders_2(sK2) ),
% 1.10/1.06      inference(cnf_transformation,[],[f66]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_26,negated_conjecture,
% 1.10/1.06      ( v1_lattice3(sK2) ),
% 1.10/1.06      inference(cnf_transformation,[],[f67]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_994,plain,
% 1.10/1.06      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.10/1.06      | k10_lattice3(sK2,X0,X1) = k13_lattice3(sK2,X0,X1) ),
% 1.10/1.06      inference(global_propositional_subsumption,
% 1.10/1.06                [status(thm)],
% 1.10/1.06                [c_990,c_27,c_26]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_995,plain,
% 1.10/1.06      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.10/1.06      | k10_lattice3(sK2,X1,X0) = k13_lattice3(sK2,X1,X0) ),
% 1.10/1.06      inference(renaming,[status(thm)],[c_994]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_1172,plain,
% 1.10/1.06      ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 1.10/1.06      | k10_lattice3(sK2,X1_47,X0_47) = k13_lattice3(sK2,X1_47,X0_47) ),
% 1.10/1.06      inference(subtyping,[status(esa)],[c_995]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_1592,plain,
% 1.10/1.06      ( k10_lattice3(sK2,X0_47,X1_47) = k13_lattice3(sK2,X0_47,X1_47)
% 1.10/1.06      | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top
% 1.10/1.06      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
% 1.10/1.06      inference(predicate_to_equality,[status(thm)],[c_1172]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_2143,plain,
% 1.10/1.06      ( k10_lattice3(sK2,sK3,X0_47) = k13_lattice3(sK2,sK3,X0_47)
% 1.10/1.06      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
% 1.10/1.06      inference(superposition,[status(thm)],[c_1573,c_1592]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_2414,plain,
% 1.10/1.06      ( k10_lattice3(sK2,sK3,sK4) = k13_lattice3(sK2,sK3,sK4) ),
% 1.10/1.06      inference(superposition,[status(thm)],[c_1572,c_2143]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_11,plain,
% 1.10/1.06      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 1.10/1.06      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.10/1.06      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 1.10/1.06      | ~ v5_orders_2(X0)
% 1.10/1.06      | ~ v1_lattice3(X0)
% 1.10/1.06      | v2_struct_0(X0)
% 1.10/1.06      | ~ l1_orders_2(X0) ),
% 1.10/1.06      inference(cnf_transformation,[],[f75]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_3,plain,
% 1.10/1.06      ( ~ v2_lattice3(X0) | ~ v2_struct_0(X0) | ~ l1_orders_2(X0) ),
% 1.10/1.06      inference(cnf_transformation,[],[f47]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_25,negated_conjecture,
% 1.10/1.06      ( v2_lattice3(sK2) ),
% 1.10/1.06      inference(cnf_transformation,[],[f68]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_646,plain,
% 1.10/1.06      ( ~ v2_struct_0(X0) | ~ l1_orders_2(X0) | sK2 != X0 ),
% 1.10/1.06      inference(resolution_lifted,[status(thm)],[c_3,c_25]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_647,plain,
% 1.10/1.06      ( ~ v2_struct_0(sK2) | ~ l1_orders_2(sK2) ),
% 1.10/1.06      inference(unflattening,[status(thm)],[c_646]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_80,plain,
% 1.10/1.06      ( ~ v2_lattice3(sK2) | ~ v2_struct_0(sK2) | ~ l1_orders_2(sK2) ),
% 1.10/1.06      inference(instantiation,[status(thm)],[c_3]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_649,plain,
% 1.10/1.06      ( ~ v2_struct_0(sK2) ),
% 1.10/1.06      inference(global_propositional_subsumption,
% 1.10/1.06                [status(thm)],
% 1.10/1.06                [c_647,c_25,c_24,c_80]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_734,plain,
% 1.10/1.06      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 1.10/1.06      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.10/1.06      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 1.10/1.06      | ~ v5_orders_2(X0)
% 1.10/1.06      | ~ v1_lattice3(X0)
% 1.10/1.06      | ~ l1_orders_2(X0)
% 1.10/1.06      | sK2 != X0 ),
% 1.10/1.06      inference(resolution_lifted,[status(thm)],[c_11,c_649]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_735,plain,
% 1.10/1.06      ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
% 1.10/1.06      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2))
% 1.10/1.06      | ~ v5_orders_2(sK2)
% 1.10/1.06      | ~ v1_lattice3(sK2)
% 1.10/1.06      | ~ l1_orders_2(sK2) ),
% 1.10/1.06      inference(unflattening,[status(thm)],[c_734]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_739,plain,
% 1.10/1.06      ( ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.10/1.06      | r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1)) ),
% 1.10/1.06      inference(global_propositional_subsumption,
% 1.10/1.06                [status(thm)],
% 1.10/1.06                [c_735,c_27,c_26,c_24]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_740,plain,
% 1.10/1.06      ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
% 1.10/1.06      inference(renaming,[status(thm)],[c_739]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_1179,plain,
% 1.10/1.06      ( r1_orders_2(sK2,X0_47,k10_lattice3(sK2,X0_47,X1_47))
% 1.10/1.06      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(k10_lattice3(sK2,X0_47,X1_47),u1_struct_0(sK2)) ),
% 1.10/1.06      inference(subtyping,[status(esa)],[c_740]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_1585,plain,
% 1.10/1.06      ( r1_orders_2(sK2,X0_47,k10_lattice3(sK2,X0_47,X1_47)) = iProver_top
% 1.10/1.06      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 1.10/1.06      | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top
% 1.10/1.06      | m1_subset_1(k10_lattice3(sK2,X0_47,X1_47),u1_struct_0(sK2)) != iProver_top ),
% 1.10/1.06      inference(predicate_to_equality,[status(thm)],[c_1179]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_4536,plain,
% 1.10/1.06      ( r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK4)) = iProver_top
% 1.10/1.06      | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 1.10/1.06      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 1.10/1.06      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 1.10/1.06      inference(superposition,[status(thm)],[c_2414,c_1585]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_4621,plain,
% 1.10/1.06      ( r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = iProver_top
% 1.10/1.06      | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 1.10/1.06      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 1.10/1.06      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 1.10/1.06      inference(light_normalisation,[status(thm)],[c_4536,c_2414]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_12,plain,
% 1.10/1.06      ( ~ r1_orders_2(X0,X1,X2)
% 1.10/1.06      | ~ r1_orders_2(X0,X1,X3)
% 1.10/1.06      | ~ r1_orders_2(X0,sK1(X0,X3,X2,X1),X1)
% 1.10/1.06      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.10/1.06      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.10/1.06      | ~ v5_orders_2(X0)
% 1.10/1.06      | ~ v2_lattice3(X0)
% 1.10/1.06      | v2_struct_0(X0)
% 1.10/1.06      | ~ l1_orders_2(X0)
% 1.10/1.06      | k11_lattice3(X0,X3,X2) = X1 ),
% 1.10/1.06      inference(cnf_transformation,[],[f62]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_195,plain,
% 1.10/1.06      ( ~ v2_lattice3(X0)
% 1.10/1.06      | ~ v5_orders_2(X0)
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.10/1.06      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.10/1.06      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.10/1.06      | ~ r1_orders_2(X0,sK1(X0,X3,X2,X1),X1)
% 1.10/1.06      | ~ r1_orders_2(X0,X1,X3)
% 1.10/1.06      | ~ r1_orders_2(X0,X1,X2)
% 1.10/1.06      | ~ l1_orders_2(X0)
% 1.10/1.06      | k11_lattice3(X0,X3,X2) = X1 ),
% 1.10/1.06      inference(global_propositional_subsumption,
% 1.10/1.06                [status(thm)],
% 1.10/1.06                [c_12,c_3]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_196,plain,
% 1.10/1.06      ( ~ r1_orders_2(X0,X1,X2)
% 1.10/1.06      | ~ r1_orders_2(X0,X1,X3)
% 1.10/1.06      | ~ r1_orders_2(X0,sK1(X0,X3,X2,X1),X1)
% 1.10/1.06      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.10/1.06      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.10/1.06      | ~ v5_orders_2(X0)
% 1.10/1.06      | ~ v2_lattice3(X0)
% 1.10/1.06      | ~ l1_orders_2(X0)
% 1.10/1.06      | k11_lattice3(X0,X3,X2) = X1 ),
% 1.10/1.06      inference(renaming,[status(thm)],[c_195]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_441,plain,
% 1.10/1.06      ( ~ r1_orders_2(X0,X1,X2)
% 1.10/1.06      | ~ r1_orders_2(X0,X1,X3)
% 1.10/1.06      | ~ r1_orders_2(X0,sK1(X0,X3,X2,X1),X1)
% 1.10/1.06      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.10/1.06      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.10/1.06      | ~ v5_orders_2(X0)
% 1.10/1.06      | ~ l1_orders_2(X0)
% 1.10/1.06      | k11_lattice3(X0,X3,X2) = X1
% 1.10/1.06      | sK2 != X0 ),
% 1.10/1.06      inference(resolution_lifted,[status(thm)],[c_196,c_25]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_442,plain,
% 1.10/1.06      ( ~ r1_orders_2(sK2,X0,X1)
% 1.10/1.06      | ~ r1_orders_2(sK2,X0,X2)
% 1.10/1.06      | ~ r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X0)
% 1.10/1.06      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 1.10/1.06      | ~ v5_orders_2(sK2)
% 1.10/1.06      | ~ l1_orders_2(sK2)
% 1.10/1.06      | k11_lattice3(sK2,X2,X1) = X0 ),
% 1.10/1.06      inference(unflattening,[status(thm)],[c_441]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_446,plain,
% 1.10/1.06      ( ~ r1_orders_2(sK2,X0,X1)
% 1.10/1.06      | ~ r1_orders_2(sK2,X0,X2)
% 1.10/1.06      | ~ r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X0)
% 1.10/1.06      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 1.10/1.06      | k11_lattice3(sK2,X2,X1) = X0 ),
% 1.10/1.06      inference(global_propositional_subsumption,
% 1.10/1.06                [status(thm)],
% 1.10/1.06                [c_442,c_27,c_24]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_447,plain,
% 1.10/1.06      ( ~ r1_orders_2(sK2,X0,X1)
% 1.10/1.06      | ~ r1_orders_2(sK2,X0,X2)
% 1.10/1.06      | ~ r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X0)
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.10/1.06      | k11_lattice3(sK2,X2,X1) = X0 ),
% 1.10/1.06      inference(renaming,[status(thm)],[c_446]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_1187,plain,
% 1.10/1.06      ( ~ r1_orders_2(sK2,X0_47,X1_47)
% 1.10/1.06      | ~ r1_orders_2(sK2,X0_47,X2_47)
% 1.10/1.06      | ~ r1_orders_2(sK2,sK1(sK2,X2_47,X1_47,X0_47),X0_47)
% 1.10/1.06      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X2_47,u1_struct_0(sK2))
% 1.10/1.06      | k11_lattice3(sK2,X2_47,X1_47) = X0_47 ),
% 1.10/1.06      inference(subtyping,[status(esa)],[c_447]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_2032,plain,
% 1.10/1.06      ( ~ r1_orders_2(sK2,X0_47,k13_lattice3(sK2,sK3,sK4))
% 1.10/1.06      | ~ r1_orders_2(sK2,X0_47,sK3)
% 1.10/1.06      | ~ r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_47),X0_47)
% 1.10/1.06      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 1.10/1.06      | k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_47 ),
% 1.10/1.06      inference(instantiation,[status(thm)],[c_1187]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_2048,plain,
% 1.10/1.06      ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_47
% 1.10/1.06      | r1_orders_2(sK2,X0_47,k13_lattice3(sK2,sK3,sK4)) != iProver_top
% 1.10/1.06      | r1_orders_2(sK2,X0_47,sK3) != iProver_top
% 1.10/1.06      | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_47),X0_47) != iProver_top
% 1.10/1.06      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 1.10/1.06      | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 1.10/1.06      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 1.10/1.06      inference(predicate_to_equality,[status(thm)],[c_2032]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_2050,plain,
% 1.10/1.06      ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
% 1.10/1.06      | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),sK3),sK3) != iProver_top
% 1.10/1.06      | r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != iProver_top
% 1.10/1.06      | r1_orders_2(sK2,sK3,sK3) != iProver_top
% 1.10/1.06      | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 1.10/1.06      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 1.10/1.06      inference(instantiation,[status(thm)],[c_2048]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_14,plain,
% 1.10/1.06      ( ~ r1_orders_2(X0,X1,X2)
% 1.10/1.06      | ~ r1_orders_2(X0,X1,X3)
% 1.10/1.06      | r1_orders_2(X0,sK1(X0,X3,X2,X1),X3)
% 1.10/1.06      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.10/1.06      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.10/1.06      | ~ v5_orders_2(X0)
% 1.10/1.06      | ~ v2_lattice3(X0)
% 1.10/1.06      | v2_struct_0(X0)
% 1.10/1.06      | ~ l1_orders_2(X0)
% 1.10/1.06      | k11_lattice3(X0,X3,X2) = X1 ),
% 1.10/1.06      inference(cnf_transformation,[],[f60]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_183,plain,
% 1.10/1.06      ( ~ v2_lattice3(X0)
% 1.10/1.06      | ~ v5_orders_2(X0)
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.10/1.06      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.10/1.06      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.10/1.06      | r1_orders_2(X0,sK1(X0,X3,X2,X1),X3)
% 1.10/1.06      | ~ r1_orders_2(X0,X1,X3)
% 1.10/1.06      | ~ r1_orders_2(X0,X1,X2)
% 1.10/1.06      | ~ l1_orders_2(X0)
% 1.10/1.06      | k11_lattice3(X0,X3,X2) = X1 ),
% 1.10/1.06      inference(global_propositional_subsumption,
% 1.10/1.06                [status(thm)],
% 1.10/1.06                [c_14,c_3]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_184,plain,
% 1.10/1.06      ( ~ r1_orders_2(X0,X1,X2)
% 1.10/1.06      | ~ r1_orders_2(X0,X1,X3)
% 1.10/1.06      | r1_orders_2(X0,sK1(X0,X3,X2,X1),X3)
% 1.10/1.06      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.10/1.06      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.10/1.06      | ~ v5_orders_2(X0)
% 1.10/1.06      | ~ v2_lattice3(X0)
% 1.10/1.06      | ~ l1_orders_2(X0)
% 1.10/1.06      | k11_lattice3(X0,X3,X2) = X1 ),
% 1.10/1.06      inference(renaming,[status(thm)],[c_183]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_507,plain,
% 1.10/1.06      ( ~ r1_orders_2(X0,X1,X2)
% 1.10/1.06      | ~ r1_orders_2(X0,X1,X3)
% 1.10/1.06      | r1_orders_2(X0,sK1(X0,X3,X2,X1),X3)
% 1.10/1.06      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.10/1.06      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.10/1.06      | ~ v5_orders_2(X0)
% 1.10/1.06      | ~ l1_orders_2(X0)
% 1.10/1.06      | k11_lattice3(X0,X3,X2) = X1
% 1.10/1.06      | sK2 != X0 ),
% 1.10/1.06      inference(resolution_lifted,[status(thm)],[c_184,c_25]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_508,plain,
% 1.10/1.06      ( ~ r1_orders_2(sK2,X0,X1)
% 1.10/1.06      | ~ r1_orders_2(sK2,X0,X2)
% 1.10/1.06      | r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X2)
% 1.10/1.06      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 1.10/1.06      | ~ v5_orders_2(sK2)
% 1.10/1.06      | ~ l1_orders_2(sK2)
% 1.10/1.06      | k11_lattice3(sK2,X2,X1) = X0 ),
% 1.10/1.06      inference(unflattening,[status(thm)],[c_507]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_510,plain,
% 1.10/1.06      ( ~ r1_orders_2(sK2,X0,X1)
% 1.10/1.06      | ~ r1_orders_2(sK2,X0,X2)
% 1.10/1.06      | r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X2)
% 1.10/1.06      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 1.10/1.06      | k11_lattice3(sK2,X2,X1) = X0 ),
% 1.10/1.06      inference(global_propositional_subsumption,
% 1.10/1.06                [status(thm)],
% 1.10/1.06                [c_508,c_27,c_24]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_511,plain,
% 1.10/1.06      ( ~ r1_orders_2(sK2,X0,X1)
% 1.10/1.06      | ~ r1_orders_2(sK2,X0,X2)
% 1.10/1.06      | r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X2)
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.10/1.06      | k11_lattice3(sK2,X2,X1) = X0 ),
% 1.10/1.06      inference(renaming,[status(thm)],[c_510]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_1185,plain,
% 1.10/1.06      ( ~ r1_orders_2(sK2,X0_47,X1_47)
% 1.10/1.06      | ~ r1_orders_2(sK2,X0_47,X2_47)
% 1.10/1.06      | r1_orders_2(sK2,sK1(sK2,X2_47,X1_47,X0_47),X2_47)
% 1.10/1.06      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X2_47,u1_struct_0(sK2))
% 1.10/1.06      | k11_lattice3(sK2,X2_47,X1_47) = X0_47 ),
% 1.10/1.06      inference(subtyping,[status(esa)],[c_511]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_2034,plain,
% 1.10/1.06      ( ~ r1_orders_2(sK2,X0_47,k13_lattice3(sK2,sK3,sK4))
% 1.10/1.06      | ~ r1_orders_2(sK2,X0_47,sK3)
% 1.10/1.06      | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_47),sK3)
% 1.10/1.06      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 1.10/1.06      | k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_47 ),
% 1.10/1.06      inference(instantiation,[status(thm)],[c_1185]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_2040,plain,
% 1.10/1.06      ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_47
% 1.10/1.06      | r1_orders_2(sK2,X0_47,k13_lattice3(sK2,sK3,sK4)) != iProver_top
% 1.10/1.06      | r1_orders_2(sK2,X0_47,sK3) != iProver_top
% 1.10/1.06      | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_47),sK3) = iProver_top
% 1.10/1.06      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 1.10/1.06      | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 1.10/1.06      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 1.10/1.06      inference(predicate_to_equality,[status(thm)],[c_2034]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_2042,plain,
% 1.10/1.06      ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
% 1.10/1.06      | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),sK3),sK3) = iProver_top
% 1.10/1.06      | r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != iProver_top
% 1.10/1.06      | r1_orders_2(sK2,sK3,sK3) != iProver_top
% 1.10/1.06      | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 1.10/1.06      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 1.10/1.06      inference(instantiation,[status(thm)],[c_2040]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_4,plain,
% 1.10/1.06      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.10/1.06      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.10/1.06      | m1_subset_1(k13_lattice3(X1,X2,X0),u1_struct_0(X1))
% 1.10/1.06      | ~ v5_orders_2(X1)
% 1.10/1.06      | ~ v1_lattice3(X1)
% 1.10/1.06      | ~ l1_orders_2(X1) ),
% 1.10/1.06      inference(cnf_transformation,[],[f48]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_1010,plain,
% 1.10/1.06      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.10/1.06      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.10/1.06      | m1_subset_1(k13_lattice3(X1,X2,X0),u1_struct_0(X1))
% 1.10/1.06      | ~ v5_orders_2(X1)
% 1.10/1.06      | ~ v1_lattice3(X1)
% 1.10/1.06      | sK2 != X1 ),
% 1.10/1.06      inference(resolution_lifted,[status(thm)],[c_4,c_24]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_1011,plain,
% 1.10/1.06      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.10/1.06      | m1_subset_1(k13_lattice3(sK2,X0,X1),u1_struct_0(sK2))
% 1.10/1.06      | ~ v5_orders_2(sK2)
% 1.10/1.06      | ~ v1_lattice3(sK2) ),
% 1.10/1.06      inference(unflattening,[status(thm)],[c_1010]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_1015,plain,
% 1.10/1.06      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.10/1.06      | m1_subset_1(k13_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
% 1.10/1.06      inference(global_propositional_subsumption,
% 1.10/1.06                [status(thm)],
% 1.10/1.06                [c_1011,c_27,c_26]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_1016,plain,
% 1.10/1.06      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.10/1.06      | m1_subset_1(k13_lattice3(sK2,X1,X0),u1_struct_0(sK2)) ),
% 1.10/1.06      inference(renaming,[status(thm)],[c_1015]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_1171,plain,
% 1.10/1.06      ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 1.10/1.06      | m1_subset_1(k13_lattice3(sK2,X1_47,X0_47),u1_struct_0(sK2)) ),
% 1.10/1.06      inference(subtyping,[status(esa)],[c_1016]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_1959,plain,
% 1.10/1.06      ( m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 1.10/1.06      inference(instantiation,[status(thm)],[c_1171]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_1960,plain,
% 1.10/1.06      ( m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) = iProver_top
% 1.10/1.06      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 1.10/1.06      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 1.10/1.06      inference(predicate_to_equality,[status(thm)],[c_1959]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_1197,plain,
% 1.10/1.06      ( X0_47 != X1_47 | X2_47 != X1_47 | X2_47 = X0_47 ),
% 1.10/1.06      theory(equality) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_1946,plain,
% 1.10/1.06      ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != X0_47
% 1.10/1.06      | sK3 != X0_47
% 1.10/1.06      | sK3 = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
% 1.10/1.06      inference(instantiation,[status(thm)],[c_1197]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_1947,plain,
% 1.10/1.06      ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3
% 1.10/1.06      | sK3 = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
% 1.10/1.06      | sK3 != sK3 ),
% 1.10/1.06      inference(instantiation,[status(thm)],[c_1946]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_19,plain,
% 1.10/1.06      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.10/1.06      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.10/1.06      | ~ v5_orders_2(X1)
% 1.10/1.06      | ~ v2_lattice3(X1)
% 1.10/1.06      | ~ l1_orders_2(X1)
% 1.10/1.06      | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0) ),
% 1.10/1.06      inference(cnf_transformation,[],[f63]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_657,plain,
% 1.10/1.06      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.10/1.06      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.10/1.06      | ~ v5_orders_2(X1)
% 1.10/1.06      | ~ l1_orders_2(X1)
% 1.10/1.06      | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0)
% 1.10/1.06      | sK2 != X1 ),
% 1.10/1.06      inference(resolution_lifted,[status(thm)],[c_19,c_25]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_658,plain,
% 1.10/1.06      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.10/1.06      | ~ v5_orders_2(sK2)
% 1.10/1.06      | ~ l1_orders_2(sK2)
% 1.10/1.06      | k12_lattice3(sK2,X0,X1) = k11_lattice3(sK2,X0,X1) ),
% 1.10/1.06      inference(unflattening,[status(thm)],[c_657]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_662,plain,
% 1.10/1.06      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.10/1.06      | k12_lattice3(sK2,X0,X1) = k11_lattice3(sK2,X0,X1) ),
% 1.10/1.06      inference(global_propositional_subsumption,
% 1.10/1.06                [status(thm)],
% 1.10/1.06                [c_658,c_27,c_24]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_663,plain,
% 1.10/1.06      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.10/1.06      | k12_lattice3(sK2,X1,X0) = k11_lattice3(sK2,X1,X0) ),
% 1.10/1.06      inference(renaming,[status(thm)],[c_662]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_1180,plain,
% 1.10/1.06      ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 1.10/1.06      | k12_lattice3(sK2,X1_47,X0_47) = k11_lattice3(sK2,X1_47,X0_47) ),
% 1.10/1.06      inference(subtyping,[status(esa)],[c_663]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_1882,plain,
% 1.10/1.06      ( ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 1.10/1.06      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
% 1.10/1.06      inference(instantiation,[status(thm)],[c_1180]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_1871,plain,
% 1.10/1.06      ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != X0_47
% 1.10/1.06      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
% 1.10/1.06      | sK3 != X0_47 ),
% 1.10/1.06      inference(instantiation,[status(thm)],[c_1197]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_1881,plain,
% 1.10/1.06      ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
% 1.10/1.06      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
% 1.10/1.06      | sK3 != k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
% 1.10/1.06      inference(instantiation,[status(thm)],[c_1871]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_2,plain,
% 1.10/1.06      ( r3_orders_2(X0,X1,X1)
% 1.10/1.06      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.10/1.06      | v2_struct_0(X0)
% 1.10/1.06      | ~ v3_orders_2(X0)
% 1.10/1.06      | ~ l1_orders_2(X0) ),
% 1.10/1.06      inference(cnf_transformation,[],[f46]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_28,negated_conjecture,
% 1.10/1.06      ( v3_orders_2(sK2) ),
% 1.10/1.06      inference(cnf_transformation,[],[f65]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_338,plain,
% 1.10/1.06      ( r3_orders_2(X0,X1,X1)
% 1.10/1.06      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.10/1.06      | v2_struct_0(X0)
% 1.10/1.06      | ~ l1_orders_2(X0)
% 1.10/1.06      | sK2 != X0 ),
% 1.10/1.06      inference(resolution_lifted,[status(thm)],[c_2,c_28]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_339,plain,
% 1.10/1.06      ( r3_orders_2(sK2,X0,X0)
% 1.10/1.06      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.10/1.06      | v2_struct_0(sK2)
% 1.10/1.06      | ~ l1_orders_2(sK2) ),
% 1.10/1.06      inference(unflattening,[status(thm)],[c_338]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_343,plain,
% 1.10/1.06      ( r3_orders_2(sK2,X0,X0)
% 1.10/1.06      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 1.10/1.06      inference(global_propositional_subsumption,
% 1.10/1.06                [status(thm)],
% 1.10/1.06                [c_339,c_25,c_24,c_80]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_344,plain,
% 1.10/1.06      ( r3_orders_2(sK2,X0,X0)
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 1.10/1.06      inference(renaming,[status(thm)],[c_343]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_1,plain,
% 1.10/1.06      ( r1_orders_2(X0,X1,X2)
% 1.10/1.06      | ~ r3_orders_2(X0,X1,X2)
% 1.10/1.06      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.10/1.06      | v2_struct_0(X0)
% 1.10/1.06      | ~ v3_orders_2(X0)
% 1.10/1.06      | ~ l1_orders_2(X0) ),
% 1.10/1.06      inference(cnf_transformation,[],[f44]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_359,plain,
% 1.10/1.06      ( r1_orders_2(X0,X1,X2)
% 1.10/1.06      | ~ r3_orders_2(X0,X1,X2)
% 1.10/1.06      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.10/1.06      | v2_struct_0(X0)
% 1.10/1.06      | ~ l1_orders_2(X0)
% 1.10/1.06      | sK2 != X0 ),
% 1.10/1.06      inference(resolution_lifted,[status(thm)],[c_1,c_28]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_360,plain,
% 1.10/1.06      ( r1_orders_2(sK2,X0,X1)
% 1.10/1.06      | ~ r3_orders_2(sK2,X0,X1)
% 1.10/1.06      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.10/1.06      | v2_struct_0(sK2)
% 1.10/1.06      | ~ l1_orders_2(sK2) ),
% 1.10/1.06      inference(unflattening,[status(thm)],[c_359]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_364,plain,
% 1.10/1.06      ( r1_orders_2(sK2,X0,X1)
% 1.10/1.06      | ~ r3_orders_2(sK2,X0,X1)
% 1.10/1.06      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 1.10/1.06      inference(global_propositional_subsumption,
% 1.10/1.06                [status(thm)],
% 1.10/1.06                [c_360,c_25,c_24,c_80]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_365,plain,
% 1.10/1.06      ( r1_orders_2(sK2,X0,X1)
% 1.10/1.06      | ~ r3_orders_2(sK2,X0,X1)
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 1.10/1.06      inference(renaming,[status(thm)],[c_364]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_422,plain,
% 1.10/1.06      ( r1_orders_2(sK2,X0,X1)
% 1.10/1.06      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X3,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.10/1.06      | X0 != X3
% 1.10/1.06      | X1 != X3
% 1.10/1.06      | sK2 != sK2 ),
% 1.10/1.06      inference(resolution_lifted,[status(thm)],[c_344,c_365]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_423,plain,
% 1.10/1.06      ( r1_orders_2(sK2,X0,X0)
% 1.10/1.06      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 1.10/1.06      inference(unflattening,[status(thm)],[c_422]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_1188,plain,
% 1.10/1.06      ( r1_orders_2(sK2,X0_47,X0_47)
% 1.10/1.06      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 1.10/1.06      | ~ m1_subset_1(X1_47,u1_struct_0(sK2)) ),
% 1.10/1.06      inference(subtyping,[status(esa)],[c_423]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_1192,plain,
% 1.10/1.06      ( ~ m1_subset_1(X0_47,u1_struct_0(sK2)) | ~ sP0_iProver_split ),
% 1.10/1.06      inference(splitting,
% 1.10/1.06                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.10/1.06                [c_1188]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_1214,plain,
% 1.10/1.06      ( m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 1.10/1.06      | sP0_iProver_split != iProver_top ),
% 1.10/1.06      inference(predicate_to_equality,[status(thm)],[c_1192]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_1216,plain,
% 1.10/1.06      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 1.10/1.06      | sP0_iProver_split != iProver_top ),
% 1.10/1.06      inference(instantiation,[status(thm)],[c_1214]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_1193,plain,
% 1.10/1.06      ( r1_orders_2(sK2,X0_47,X0_47)
% 1.10/1.06      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 1.10/1.06      | ~ sP1_iProver_split ),
% 1.10/1.06      inference(splitting,
% 1.10/1.06                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 1.10/1.06                [c_1188]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_1211,plain,
% 1.10/1.06      ( r1_orders_2(sK2,X0_47,X0_47) = iProver_top
% 1.10/1.06      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 1.10/1.06      | sP1_iProver_split != iProver_top ),
% 1.10/1.06      inference(predicate_to_equality,[status(thm)],[c_1193]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_1213,plain,
% 1.10/1.06      ( r1_orders_2(sK2,sK3,sK3) = iProver_top
% 1.10/1.06      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 1.10/1.06      | sP1_iProver_split != iProver_top ),
% 1.10/1.06      inference(instantiation,[status(thm)],[c_1211]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_1194,plain,
% 1.10/1.06      ( sP1_iProver_split | sP0_iProver_split ),
% 1.10/1.06      inference(splitting,
% 1.10/1.06                [splitting(split),new_symbols(definition,[])],
% 1.10/1.06                [c_1188]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_1210,plain,
% 1.10/1.06      ( sP1_iProver_split = iProver_top
% 1.10/1.06      | sP0_iProver_split = iProver_top ),
% 1.10/1.06      inference(predicate_to_equality,[status(thm)],[c_1194]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_21,negated_conjecture,
% 1.10/1.06      ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
% 1.10/1.06      inference(cnf_transformation,[],[f72]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_1191,negated_conjecture,
% 1.10/1.06      ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
% 1.10/1.06      inference(subtyping,[status(esa)],[c_21]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_1196,plain,( X0_47 = X0_47 ),theory(equality) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_1207,plain,
% 1.10/1.06      ( sK3 = sK3 ),
% 1.10/1.06      inference(instantiation,[status(thm)],[c_1196]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_35,plain,
% 1.10/1.06      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 1.10/1.06      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(c_34,plain,
% 1.10/1.06      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 1.10/1.06      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.10/1.06  
% 1.10/1.06  cnf(contradiction,plain,
% 1.10/1.06      ( $false ),
% 1.10/1.06      inference(minisat,
% 1.10/1.06                [status(thm)],
% 1.10/1.06                [c_4621,c_2050,c_2042,c_1960,c_1959,c_1947,c_1882,c_1881,
% 1.10/1.06                 c_1216,c_1213,c_1210,c_1191,c_1207,c_35,c_22,c_34,c_23]) ).
% 1.10/1.06  
% 1.10/1.06  
% 1.10/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 1.10/1.06  
% 1.10/1.06  ------                               Statistics
% 1.10/1.06  
% 1.10/1.06  ------ General
% 1.10/1.06  
% 1.10/1.06  abstr_ref_over_cycles:                  0
% 1.10/1.06  abstr_ref_under_cycles:                 0
% 1.10/1.06  gc_basic_clause_elim:                   0
% 1.10/1.06  forced_gc_time:                         0
% 1.10/1.06  parsing_time:                           0.012
% 1.10/1.06  unif_index_cands_time:                  0.
% 1.10/1.06  unif_index_add_time:                    0.
% 1.10/1.06  orderings_time:                         0.
% 1.10/1.06  out_proof_time:                         0.011
% 1.10/1.06  total_time:                             0.15
% 1.10/1.06  num_of_symbols:                         52
% 1.10/1.06  num_of_terms:                           4394
% 1.10/1.06  
% 1.10/1.06  ------ Preprocessing
% 1.10/1.06  
% 1.10/1.06  num_of_splits:                          2
% 1.10/1.06  num_of_split_atoms:                     2
% 1.10/1.06  num_of_reused_defs:                     0
% 1.10/1.06  num_eq_ax_congr_red:                    48
% 1.10/1.06  num_of_sem_filtered_clauses:            3
% 1.10/1.06  num_of_subtypes:                        3
% 1.10/1.06  monotx_restored_types:                  0
% 1.10/1.06  sat_num_of_epr_types:                   0
% 1.10/1.06  sat_num_of_non_cyclic_types:            0
% 1.10/1.06  sat_guarded_non_collapsed_types:        1
% 1.10/1.06  num_pure_diseq_elim:                    0
% 1.10/1.06  simp_replaced_by:                       0
% 1.10/1.06  res_preprocessed:                       107
% 1.10/1.06  prep_upred:                             0
% 1.10/1.06  prep_unflattend:                        23
% 1.10/1.06  smt_new_axioms:                         0
% 1.10/1.06  pred_elim_cands:                        2
% 1.10/1.06  pred_elim:                              7
% 1.10/1.06  pred_elim_cl:                           8
% 1.10/1.06  pred_elim_cycles:                       9
% 1.10/1.06  merged_defs:                            0
% 1.10/1.06  merged_defs_ncl:                        0
% 1.10/1.06  bin_hyper_res:                          0
% 1.10/1.06  prep_cycles:                            4
% 1.10/1.06  pred_elim_time:                         0.011
% 1.10/1.06  splitting_time:                         0.
% 1.10/1.06  sem_filter_time:                        0.
% 1.10/1.06  monotx_time:                            0.
% 1.10/1.06  subtype_inf_time:                       0.
% 1.10/1.06  
% 1.10/1.06  ------ Problem properties
% 1.10/1.06  
% 1.10/1.06  clauses:                                23
% 1.10/1.06  conjectures:                            3
% 1.10/1.06  epr:                                    1
% 1.10/1.06  horn:                                   16
% 1.10/1.06  ground:                                 4
% 1.10/1.06  unary:                                  3
% 1.10/1.06  binary:                                 2
% 1.10/1.06  lits:                                   105
% 1.10/1.06  lits_eq:                                11
% 1.10/1.06  fd_pure:                                0
% 1.10/1.06  fd_pseudo:                              0
% 1.10/1.06  fd_cond:                                0
% 1.10/1.06  fd_pseudo_cond:                         8
% 1.10/1.06  ac_symbols:                             0
% 1.10/1.06  
% 1.10/1.06  ------ Propositional Solver
% 1.10/1.06  
% 1.10/1.06  prop_solver_calls:                      28
% 1.10/1.06  prop_fast_solver_calls:                 1503
% 1.10/1.06  smt_solver_calls:                       0
% 1.10/1.06  smt_fast_solver_calls:                  0
% 1.10/1.06  prop_num_of_clauses:                    1372
% 1.10/1.06  prop_preprocess_simplified:             4652
% 1.10/1.06  prop_fo_subsumed:                       60
% 1.10/1.06  prop_solver_time:                       0.
% 1.10/1.06  smt_solver_time:                        0.
% 1.10/1.06  smt_fast_solver_time:                   0.
% 1.10/1.06  prop_fast_solver_time:                  0.
% 1.10/1.06  prop_unsat_core_time:                   0.
% 1.10/1.06  
% 1.10/1.06  ------ QBF
% 1.10/1.06  
% 1.10/1.06  qbf_q_res:                              0
% 1.10/1.06  qbf_num_tautologies:                    0
% 1.10/1.06  qbf_prep_cycles:                        0
% 1.10/1.06  
% 1.10/1.06  ------ BMC1
% 1.10/1.06  
% 1.10/1.06  bmc1_current_bound:                     -1
% 1.10/1.06  bmc1_last_solved_bound:                 -1
% 1.10/1.06  bmc1_unsat_core_size:                   -1
% 1.10/1.06  bmc1_unsat_core_parents_size:           -1
% 1.10/1.06  bmc1_merge_next_fun:                    0
% 1.10/1.06  bmc1_unsat_core_clauses_time:           0.
% 1.10/1.06  
% 1.10/1.06  ------ Instantiation
% 1.10/1.06  
% 1.10/1.06  inst_num_of_clauses:                    367
% 1.10/1.06  inst_num_in_passive:                    36
% 1.10/1.06  inst_num_in_active:                     219
% 1.10/1.06  inst_num_in_unprocessed:                112
% 1.10/1.06  inst_num_of_loops:                      240
% 1.10/1.06  inst_num_of_learning_restarts:          0
% 1.10/1.06  inst_num_moves_active_passive:          17
% 1.10/1.06  inst_lit_activity:                      0
% 1.10/1.06  inst_lit_activity_moves:                0
% 1.10/1.06  inst_num_tautologies:                   0
% 1.10/1.06  inst_num_prop_implied:                  0
% 1.10/1.06  inst_num_existing_simplified:           0
% 1.10/1.06  inst_num_eq_res_simplified:             0
% 1.10/1.06  inst_num_child_elim:                    0
% 1.10/1.06  inst_num_of_dismatching_blockings:      210
% 1.10/1.06  inst_num_of_non_proper_insts:           372
% 1.10/1.06  inst_num_of_duplicates:                 0
% 1.10/1.06  inst_inst_num_from_inst_to_res:         0
% 1.10/1.06  inst_dismatching_checking_time:         0.
% 1.10/1.06  
% 1.10/1.06  ------ Resolution
% 1.10/1.06  
% 1.10/1.06  res_num_of_clauses:                     0
% 1.10/1.06  res_num_in_passive:                     0
% 1.10/1.06  res_num_in_active:                      0
% 1.10/1.06  res_num_of_loops:                       111
% 1.10/1.06  res_forward_subset_subsumed:            33
% 1.10/1.06  res_backward_subset_subsumed:           0
% 1.10/1.06  res_forward_subsumed:                   0
% 1.10/1.06  res_backward_subsumed:                  0
% 1.10/1.06  res_forward_subsumption_resolution:     0
% 1.10/1.06  res_backward_subsumption_resolution:    0
% 1.10/1.06  res_clause_to_clause_subsumption:       501
% 1.10/1.06  res_orphan_elimination:                 0
% 1.10/1.06  res_tautology_del:                      34
% 1.10/1.06  res_num_eq_res_simplified:              0
% 1.10/1.06  res_num_sel_changes:                    0
% 1.10/1.06  res_moves_from_active_to_pass:          0
% 1.10/1.06  
% 1.10/1.06  ------ Superposition
% 1.10/1.06  
% 1.10/1.06  sup_time_total:                         0.
% 1.10/1.06  sup_time_generating:                    0.
% 1.10/1.06  sup_time_sim_full:                      0.
% 1.10/1.06  sup_time_sim_immed:                     0.
% 1.10/1.06  
% 1.10/1.06  sup_num_of_clauses:                     94
% 1.10/1.06  sup_num_in_active:                      48
% 1.10/1.06  sup_num_in_passive:                     46
% 1.10/1.06  sup_num_of_loops:                       47
% 1.10/1.06  sup_fw_superposition:                   52
% 1.10/1.06  sup_bw_superposition:                   22
% 1.10/1.06  sup_immediate_simplified:               12
% 1.10/1.06  sup_given_eliminated:                   0
% 1.10/1.06  comparisons_done:                       0
% 1.10/1.06  comparisons_avoided:                    0
% 1.10/1.06  
% 1.10/1.06  ------ Simplifications
% 1.10/1.06  
% 1.10/1.06  
% 1.10/1.06  sim_fw_subset_subsumed:                 0
% 1.10/1.06  sim_bw_subset_subsumed:                 0
% 1.10/1.06  sim_fw_subsumed:                        0
% 1.10/1.06  sim_bw_subsumed:                        0
% 1.10/1.06  sim_fw_subsumption_res:                 0
% 1.10/1.06  sim_bw_subsumption_res:                 0
% 1.10/1.06  sim_tautology_del:                      0
% 1.10/1.06  sim_eq_tautology_del:                   0
% 1.10/1.06  sim_eq_res_simp:                        0
% 1.10/1.06  sim_fw_demodulated:                     0
% 1.10/1.06  sim_bw_demodulated:                     0
% 1.10/1.06  sim_light_normalised:                   12
% 1.10/1.06  sim_joinable_taut:                      0
% 1.10/1.06  sim_joinable_simp:                      0
% 1.10/1.06  sim_ac_normalised:                      0
% 1.10/1.06  sim_smt_subsumption:                    0
% 1.10/1.06  
%------------------------------------------------------------------------------
