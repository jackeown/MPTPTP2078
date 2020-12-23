%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:05 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 850 expanded)
%              Number of clauses        :  102 ( 218 expanded)
%              Number of leaves         :   16 ( 259 expanded)
%              Depth                    :   20
%              Number of atoms          :  953 (5426 expanded)
%              Number of equality atoms :  166 ( 827 expanded)
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

fof(f67,plain,(
    v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f66,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f69,plain,(
    l1_orders_2(sK2) ),
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
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

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

fof(f68,plain,(
    v2_lattice3(sK2) ),
    inference(cnf_transformation,[],[f43])).

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

cnf(c_26,negated_conjecture,
    ( v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_657,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_26])).

cnf(c_658,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k10_lattice3(sK2,X0,X1) = k13_lattice3(sK2,X0,X1) ),
    inference(unflattening,[status(thm)],[c_657])).

cnf(c_27,negated_conjecture,
    ( v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_24,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_662,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k10_lattice3(sK2,X0,X1) = k13_lattice3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_658,c_27,c_24])).

cnf(c_663,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k10_lattice3(sK2,X1,X0) = k13_lattice3(sK2,X1,X0) ),
    inference(renaming,[status(thm)],[c_662])).

cnf(c_1180,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | k10_lattice3(sK2,X1_47,X0_47) = k13_lattice3(sK2,X1_47,X0_47) ),
    inference(subtyping,[status(esa)],[c_663])).

cnf(c_1584,plain,
    ( k10_lattice3(sK2,X0_47,X1_47) = k13_lattice3(sK2,X0_47,X1_47)
    | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1180])).

cnf(c_1858,plain,
    ( k10_lattice3(sK2,sK3,X0_47) = k13_lattice3(sK2,sK3,X0_47)
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1573,c_1584])).

cnf(c_1985,plain,
    ( k10_lattice3(sK2,sK3,sK4) = k13_lattice3(sK2,sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1572,c_1858])).

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
    ( ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_164,plain,
    ( ~ v1_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_3])).

cnf(c_165,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_164])).

cnf(c_626,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_165,c_26])).

cnf(c_627,plain,
    ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_626])).

cnf(c_629,plain,
    ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_627,c_27,c_24])).

cnf(c_630,plain,
    ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_629])).

cnf(c_1181,plain,
    ( r1_orders_2(sK2,X0_47,k10_lattice3(sK2,X0_47,X1_47))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X0_47,X1_47),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_630])).

cnf(c_1583,plain,
    ( r1_orders_2(sK2,X0_47,k10_lattice3(sK2,X0_47,X1_47)) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k10_lattice3(sK2,X0_47,X1_47),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1181])).

cnf(c_3205,plain,
    ( r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK4)) = iProver_top
    | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1985,c_1583])).

cnf(c_3250,plain,
    ( r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = iProver_top
    | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3205,c_1985])).

cnf(c_14,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK1(X0,X3,X2,X1),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_646,plain,
    ( ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_26])).

cnf(c_647,plain,
    ( ~ v2_struct_0(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_646])).

cnf(c_80,plain,
    ( ~ v1_lattice3(sK2)
    | ~ v2_struct_0(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_649,plain,
    ( ~ v2_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_647,c_26,c_24,c_80])).

cnf(c_869,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK1(X0,X3,X2,X1),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_649])).

cnf(c_870,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ v2_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k11_lattice3(sK2,X2,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_869])).

cnf(c_25,negated_conjecture,
    ( v2_lattice3(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_874,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X2)
    | ~ r1_orders_2(sK2,X0,X2)
    | ~ r1_orders_2(sK2,X0,X1)
    | k11_lattice3(sK2,X2,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_870,c_27,c_25,c_24])).

cnf(c_875,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k11_lattice3(sK2,X2,X1) = X0 ),
    inference(renaming,[status(thm)],[c_874])).

cnf(c_1174,plain,
    ( ~ r1_orders_2(sK2,X0_47,X1_47)
    | ~ r1_orders_2(sK2,X0_47,X2_47)
    | r1_orders_2(sK2,sK1(sK2,X2_47,X1_47,X0_47),X2_47)
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X2_47,u1_struct_0(sK2))
    | k11_lattice3(sK2,X2_47,X1_47) = X0_47 ),
    inference(subtyping,[status(esa)],[c_875])).

cnf(c_2032,plain,
    ( ~ r1_orders_2(sK2,X0_47,k13_lattice3(sK2,sK3,sK4))
    | ~ r1_orders_2(sK2,X0_47,sK3)
    | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_47),sK3)
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_47 ),
    inference(instantiation,[status(thm)],[c_1174])).

cnf(c_2048,plain,
    ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_47
    | r1_orders_2(sK2,X0_47,k13_lattice3(sK2,sK3,sK4)) != iProver_top
    | r1_orders_2(sK2,X0_47,sK3) != iProver_top
    | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_47),sK3) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2032])).

cnf(c_2050,plain,
    ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
    | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),sK3),sK3) = iProver_top
    | r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != iProver_top
    | r1_orders_2(sK2,sK3,sK3) != iProver_top
    | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2048])).

cnf(c_12,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK1(X0,X3,X2,X1),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_931,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK1(X0,X3,X2,X1),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_649])).

cnf(c_932,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | ~ r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ v2_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k11_lattice3(sK2,X2,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_931])).

cnf(c_936,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X0)
    | ~ r1_orders_2(sK2,X0,X2)
    | ~ r1_orders_2(sK2,X0,X1)
    | k11_lattice3(sK2,X2,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_932,c_27,c_25,c_24])).

cnf(c_937,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | ~ r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k11_lattice3(sK2,X2,X1) = X0 ),
    inference(renaming,[status(thm)],[c_936])).

cnf(c_1172,plain,
    ( ~ r1_orders_2(sK2,X0_47,X1_47)
    | ~ r1_orders_2(sK2,X0_47,X2_47)
    | ~ r1_orders_2(sK2,sK1(sK2,X2_47,X1_47,X0_47),X0_47)
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X2_47,u1_struct_0(sK2))
    | k11_lattice3(sK2,X2_47,X1_47) = X0_47 ),
    inference(subtyping,[status(esa)],[c_937])).

cnf(c_2034,plain,
    ( ~ r1_orders_2(sK2,X0_47,k13_lattice3(sK2,sK3,sK4))
    | ~ r1_orders_2(sK2,X0_47,sK3)
    | ~ r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_47),X0_47)
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_47 ),
    inference(instantiation,[status(thm)],[c_1172])).

cnf(c_2040,plain,
    ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_47
    | r1_orders_2(sK2,X0_47,k13_lattice3(sK2,sK3,sK4)) != iProver_top
    | r1_orders_2(sK2,X0_47,sK3) != iProver_top
    | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_47),X0_47) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2034])).

cnf(c_2042,plain,
    ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
    | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),sK3),sK3) != iProver_top
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

cnf(c_678,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k13_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_26])).

cnf(c_679,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(k13_lattice3(sK2,X0,X1),u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_678])).

cnf(c_683,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(k13_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_679,c_27,c_24])).

cnf(c_684,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(k13_lattice3(sK2,X1,X0),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_683])).

cnf(c_1179,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | m1_subset_1(k13_lattice3(sK2,X1_47,X0_47),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_684])).

cnf(c_1959,plain,
    ( m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1179])).

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
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1014,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_24])).

cnf(c_1015,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v2_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | k12_lattice3(sK2,X0,X1) = k11_lattice3(sK2,X0,X1) ),
    inference(unflattening,[status(thm)],[c_1014])).

cnf(c_1019,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k12_lattice3(sK2,X0,X1) = k11_lattice3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1015,c_27,c_25])).

cnf(c_1020,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k12_lattice3(sK2,X1,X0) = k11_lattice3(sK2,X1,X0) ),
    inference(renaming,[status(thm)],[c_1019])).

cnf(c_1171,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | k12_lattice3(sK2,X1_47,X0_47) = k11_lattice3(sK2,X1_47,X0_47) ),
    inference(subtyping,[status(esa)],[c_1020])).

cnf(c_1882,plain,
    ( ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1171])).

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
    inference(global_propositional_subsumption,[status(thm)],[c_339,c_26,c_24,c_80])).

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
    inference(global_propositional_subsumption,[status(thm)],[c_360,c_26,c_24,c_80])).

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
    inference(minisat,[status(thm)],[c_3250,c_2050,c_2042,c_1960,c_1959,c_1947,c_1882,c_1881,c_1216,c_1213,c_1210,c_1191,c_1207,c_35,c_22,c_34,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:51:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.26/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/0.99  
% 2.26/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.26/0.99  
% 2.26/0.99  ------  iProver source info
% 2.26/0.99  
% 2.26/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.26/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.26/0.99  git: non_committed_changes: false
% 2.26/0.99  git: last_make_outside_of_git: false
% 2.26/0.99  
% 2.26/0.99  ------ 
% 2.26/0.99  
% 2.26/0.99  ------ Input Options
% 2.26/0.99  
% 2.26/0.99  --out_options                           all
% 2.26/0.99  --tptp_safe_out                         true
% 2.26/0.99  --problem_path                          ""
% 2.26/0.99  --include_path                          ""
% 2.26/0.99  --clausifier                            res/vclausify_rel
% 2.26/0.99  --clausifier_options                    --mode clausify
% 2.26/0.99  --stdin                                 false
% 2.26/0.99  --stats_out                             all
% 2.26/0.99  
% 2.26/0.99  ------ General Options
% 2.26/0.99  
% 2.26/0.99  --fof                                   false
% 2.26/0.99  --time_out_real                         305.
% 2.26/0.99  --time_out_virtual                      -1.
% 2.26/0.99  --symbol_type_check                     false
% 2.26/0.99  --clausify_out                          false
% 2.26/0.99  --sig_cnt_out                           false
% 2.26/0.99  --trig_cnt_out                          false
% 2.26/0.99  --trig_cnt_out_tolerance                1.
% 2.26/0.99  --trig_cnt_out_sk_spl                   false
% 2.26/0.99  --abstr_cl_out                          false
% 2.26/0.99  
% 2.26/0.99  ------ Global Options
% 2.26/0.99  
% 2.26/0.99  --schedule                              default
% 2.26/0.99  --add_important_lit                     false
% 2.26/0.99  --prop_solver_per_cl                    1000
% 2.26/0.99  --min_unsat_core                        false
% 2.26/0.99  --soft_assumptions                      false
% 2.26/0.99  --soft_lemma_size                       3
% 2.26/0.99  --prop_impl_unit_size                   0
% 2.26/0.99  --prop_impl_unit                        []
% 2.26/0.99  --share_sel_clauses                     true
% 2.26/0.99  --reset_solvers                         false
% 2.26/0.99  --bc_imp_inh                            [conj_cone]
% 2.26/0.99  --conj_cone_tolerance                   3.
% 2.26/0.99  --extra_neg_conj                        none
% 2.26/0.99  --large_theory_mode                     true
% 2.26/0.99  --prolific_symb_bound                   200
% 2.26/0.99  --lt_threshold                          2000
% 2.26/0.99  --clause_weak_htbl                      true
% 2.26/0.99  --gc_record_bc_elim                     false
% 2.26/0.99  
% 2.26/0.99  ------ Preprocessing Options
% 2.26/0.99  
% 2.26/0.99  --preprocessing_flag                    true
% 2.26/0.99  --time_out_prep_mult                    0.1
% 2.26/0.99  --splitting_mode                        input
% 2.26/0.99  --splitting_grd                         true
% 2.26/0.99  --splitting_cvd                         false
% 2.26/0.99  --splitting_cvd_svl                     false
% 2.26/0.99  --splitting_nvd                         32
% 2.26/0.99  --sub_typing                            true
% 2.26/0.99  --prep_gs_sim                           true
% 2.26/0.99  --prep_unflatten                        true
% 2.26/0.99  --prep_res_sim                          true
% 2.26/0.99  --prep_upred                            true
% 2.26/0.99  --prep_sem_filter                       exhaustive
% 2.26/0.99  --prep_sem_filter_out                   false
% 2.26/0.99  --pred_elim                             true
% 2.26/0.99  --res_sim_input                         true
% 2.26/0.99  --eq_ax_congr_red                       true
% 2.26/0.99  --pure_diseq_elim                       true
% 2.26/0.99  --brand_transform                       false
% 2.26/0.99  --non_eq_to_eq                          false
% 2.26/0.99  --prep_def_merge                        true
% 2.26/0.99  --prep_def_merge_prop_impl              false
% 2.26/0.99  --prep_def_merge_mbd                    true
% 2.26/0.99  --prep_def_merge_tr_red                 false
% 2.26/0.99  --prep_def_merge_tr_cl                  false
% 2.26/0.99  --smt_preprocessing                     true
% 2.26/0.99  --smt_ac_axioms                         fast
% 2.26/0.99  --preprocessed_out                      false
% 2.26/0.99  --preprocessed_stats                    false
% 2.26/0.99  
% 2.26/0.99  ------ Abstraction refinement Options
% 2.26/0.99  
% 2.26/0.99  --abstr_ref                             []
% 2.26/0.99  --abstr_ref_prep                        false
% 2.26/0.99  --abstr_ref_until_sat                   false
% 2.26/0.99  --abstr_ref_sig_restrict                funpre
% 2.26/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.26/0.99  --abstr_ref_under                       []
% 2.26/0.99  
% 2.26/0.99  ------ SAT Options
% 2.26/0.99  
% 2.26/0.99  --sat_mode                              false
% 2.26/0.99  --sat_fm_restart_options                ""
% 2.26/0.99  --sat_gr_def                            false
% 2.26/0.99  --sat_epr_types                         true
% 2.26/0.99  --sat_non_cyclic_types                  false
% 2.26/0.99  --sat_finite_models                     false
% 2.26/0.99  --sat_fm_lemmas                         false
% 2.26/0.99  --sat_fm_prep                           false
% 2.26/0.99  --sat_fm_uc_incr                        true
% 2.26/0.99  --sat_out_model                         small
% 2.26/0.99  --sat_out_clauses                       false
% 2.26/0.99  
% 2.26/0.99  ------ QBF Options
% 2.26/0.99  
% 2.26/0.99  --qbf_mode                              false
% 2.26/0.99  --qbf_elim_univ                         false
% 2.26/0.99  --qbf_dom_inst                          none
% 2.26/0.99  --qbf_dom_pre_inst                      false
% 2.26/0.99  --qbf_sk_in                             false
% 2.26/0.99  --qbf_pred_elim                         true
% 2.26/0.99  --qbf_split                             512
% 2.26/0.99  
% 2.26/0.99  ------ BMC1 Options
% 2.26/0.99  
% 2.26/0.99  --bmc1_incremental                      false
% 2.26/0.99  --bmc1_axioms                           reachable_all
% 2.26/0.99  --bmc1_min_bound                        0
% 2.26/0.99  --bmc1_max_bound                        -1
% 2.26/0.99  --bmc1_max_bound_default                -1
% 2.26/0.99  --bmc1_symbol_reachability              true
% 2.26/0.99  --bmc1_property_lemmas                  false
% 2.26/0.99  --bmc1_k_induction                      false
% 2.26/0.99  --bmc1_non_equiv_states                 false
% 2.26/0.99  --bmc1_deadlock                         false
% 2.26/0.99  --bmc1_ucm                              false
% 2.26/0.99  --bmc1_add_unsat_core                   none
% 2.26/0.99  --bmc1_unsat_core_children              false
% 2.26/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.26/0.99  --bmc1_out_stat                         full
% 2.26/0.99  --bmc1_ground_init                      false
% 2.26/0.99  --bmc1_pre_inst_next_state              false
% 2.26/0.99  --bmc1_pre_inst_state                   false
% 2.26/0.99  --bmc1_pre_inst_reach_state             false
% 2.26/0.99  --bmc1_out_unsat_core                   false
% 2.26/0.99  --bmc1_aig_witness_out                  false
% 2.26/0.99  --bmc1_verbose                          false
% 2.26/0.99  --bmc1_dump_clauses_tptp                false
% 2.26/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.26/0.99  --bmc1_dump_file                        -
% 2.26/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.26/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.26/0.99  --bmc1_ucm_extend_mode                  1
% 2.26/0.99  --bmc1_ucm_init_mode                    2
% 2.26/0.99  --bmc1_ucm_cone_mode                    none
% 2.26/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.26/0.99  --bmc1_ucm_relax_model                  4
% 2.26/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.26/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.26/0.99  --bmc1_ucm_layered_model                none
% 2.26/0.99  --bmc1_ucm_max_lemma_size               10
% 2.26/0.99  
% 2.26/0.99  ------ AIG Options
% 2.26/0.99  
% 2.26/0.99  --aig_mode                              false
% 2.26/0.99  
% 2.26/0.99  ------ Instantiation Options
% 2.26/0.99  
% 2.26/0.99  --instantiation_flag                    true
% 2.26/0.99  --inst_sos_flag                         false
% 2.26/0.99  --inst_sos_phase                        true
% 2.26/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.26/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.26/0.99  --inst_lit_sel_side                     num_symb
% 2.26/0.99  --inst_solver_per_active                1400
% 2.26/0.99  --inst_solver_calls_frac                1.
% 2.26/0.99  --inst_passive_queue_type               priority_queues
% 2.26/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.26/0.99  --inst_passive_queues_freq              [25;2]
% 2.26/0.99  --inst_dismatching                      true
% 2.26/0.99  --inst_eager_unprocessed_to_passive     true
% 2.26/0.99  --inst_prop_sim_given                   true
% 2.26/0.99  --inst_prop_sim_new                     false
% 2.26/0.99  --inst_subs_new                         false
% 2.26/0.99  --inst_eq_res_simp                      false
% 2.26/0.99  --inst_subs_given                       false
% 2.26/0.99  --inst_orphan_elimination               true
% 2.26/0.99  --inst_learning_loop_flag               true
% 2.26/0.99  --inst_learning_start                   3000
% 2.26/0.99  --inst_learning_factor                  2
% 2.26/0.99  --inst_start_prop_sim_after_learn       3
% 2.26/0.99  --inst_sel_renew                        solver
% 2.26/0.99  --inst_lit_activity_flag                true
% 2.26/0.99  --inst_restr_to_given                   false
% 2.26/0.99  --inst_activity_threshold               500
% 2.26/0.99  --inst_out_proof                        true
% 2.26/0.99  
% 2.26/0.99  ------ Resolution Options
% 2.26/0.99  
% 2.26/0.99  --resolution_flag                       true
% 2.26/0.99  --res_lit_sel                           adaptive
% 2.26/0.99  --res_lit_sel_side                      none
% 2.26/0.99  --res_ordering                          kbo
% 2.26/0.99  --res_to_prop_solver                    active
% 2.26/0.99  --res_prop_simpl_new                    false
% 2.26/0.99  --res_prop_simpl_given                  true
% 2.26/0.99  --res_passive_queue_type                priority_queues
% 2.26/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.26/0.99  --res_passive_queues_freq               [15;5]
% 2.26/0.99  --res_forward_subs                      full
% 2.26/0.99  --res_backward_subs                     full
% 2.26/0.99  --res_forward_subs_resolution           true
% 2.26/0.99  --res_backward_subs_resolution          true
% 2.26/0.99  --res_orphan_elimination                true
% 2.26/0.99  --res_time_limit                        2.
% 2.26/0.99  --res_out_proof                         true
% 2.26/0.99  
% 2.26/0.99  ------ Superposition Options
% 2.26/0.99  
% 2.26/0.99  --superposition_flag                    true
% 2.26/0.99  --sup_passive_queue_type                priority_queues
% 2.26/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.26/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.26/0.99  --demod_completeness_check              fast
% 2.26/0.99  --demod_use_ground                      true
% 2.26/0.99  --sup_to_prop_solver                    passive
% 2.26/0.99  --sup_prop_simpl_new                    true
% 2.26/0.99  --sup_prop_simpl_given                  true
% 2.26/0.99  --sup_fun_splitting                     false
% 2.26/0.99  --sup_smt_interval                      50000
% 2.26/0.99  
% 2.26/0.99  ------ Superposition Simplification Setup
% 2.26/0.99  
% 2.26/0.99  --sup_indices_passive                   []
% 2.26/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.26/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.26/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.26/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.26/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.26/0.99  --sup_full_bw                           [BwDemod]
% 2.26/0.99  --sup_immed_triv                        [TrivRules]
% 2.26/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.26/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.26/0.99  --sup_immed_bw_main                     []
% 2.26/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.26/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.26/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.26/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.26/0.99  
% 2.26/0.99  ------ Combination Options
% 2.26/0.99  
% 2.26/0.99  --comb_res_mult                         3
% 2.26/0.99  --comb_sup_mult                         2
% 2.26/0.99  --comb_inst_mult                        10
% 2.26/0.99  
% 2.26/0.99  ------ Debug Options
% 2.26/0.99  
% 2.26/0.99  --dbg_backtrace                         false
% 2.26/0.99  --dbg_dump_prop_clauses                 false
% 2.26/0.99  --dbg_dump_prop_clauses_file            -
% 2.26/0.99  --dbg_out_stat                          false
% 2.26/0.99  ------ Parsing...
% 2.26/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.26/0.99  
% 2.26/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.26/0.99  
% 2.26/0.99  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.26/0.99  
% 2.26/0.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.26/0.99  ------ Proving...
% 2.26/0.99  ------ Problem Properties 
% 2.26/0.99  
% 2.26/0.99  
% 2.26/0.99  clauses                                 23
% 2.26/0.99  conjectures                             3
% 2.26/0.99  EPR                                     1
% 2.26/0.99  Horn                                    16
% 2.26/0.99  unary                                   3
% 2.26/0.99  binary                                  2
% 2.26/0.99  lits                                    105
% 2.26/0.99  lits eq                                 11
% 2.26/0.99  fd_pure                                 0
% 2.26/0.99  fd_pseudo                               0
% 2.26/0.99  fd_cond                                 0
% 2.26/0.99  fd_pseudo_cond                          8
% 2.26/0.99  AC symbols                              0
% 2.26/0.99  
% 2.26/0.99  ------ Schedule dynamic 5 is on 
% 2.26/0.99  
% 2.26/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.26/0.99  
% 2.26/0.99  
% 2.26/0.99  ------ 
% 2.26/0.99  Current options:
% 2.26/0.99  ------ 
% 2.26/0.99  
% 2.26/0.99  ------ Input Options
% 2.26/0.99  
% 2.26/0.99  --out_options                           all
% 2.26/0.99  --tptp_safe_out                         true
% 2.26/0.99  --problem_path                          ""
% 2.26/0.99  --include_path                          ""
% 2.26/0.99  --clausifier                            res/vclausify_rel
% 2.26/0.99  --clausifier_options                    --mode clausify
% 2.26/0.99  --stdin                                 false
% 2.26/0.99  --stats_out                             all
% 2.26/0.99  
% 2.26/0.99  ------ General Options
% 2.26/0.99  
% 2.26/0.99  --fof                                   false
% 2.26/0.99  --time_out_real                         305.
% 2.26/0.99  --time_out_virtual                      -1.
% 2.26/0.99  --symbol_type_check                     false
% 2.26/0.99  --clausify_out                          false
% 2.26/0.99  --sig_cnt_out                           false
% 2.26/0.99  --trig_cnt_out                          false
% 2.26/0.99  --trig_cnt_out_tolerance                1.
% 2.26/0.99  --trig_cnt_out_sk_spl                   false
% 2.26/0.99  --abstr_cl_out                          false
% 2.26/0.99  
% 2.26/0.99  ------ Global Options
% 2.26/0.99  
% 2.26/0.99  --schedule                              default
% 2.26/0.99  --add_important_lit                     false
% 2.26/0.99  --prop_solver_per_cl                    1000
% 2.26/0.99  --min_unsat_core                        false
% 2.26/0.99  --soft_assumptions                      false
% 2.26/0.99  --soft_lemma_size                       3
% 2.26/0.99  --prop_impl_unit_size                   0
% 2.26/0.99  --prop_impl_unit                        []
% 2.26/0.99  --share_sel_clauses                     true
% 2.26/0.99  --reset_solvers                         false
% 2.26/0.99  --bc_imp_inh                            [conj_cone]
% 2.26/0.99  --conj_cone_tolerance                   3.
% 2.26/0.99  --extra_neg_conj                        none
% 2.26/0.99  --large_theory_mode                     true
% 2.26/0.99  --prolific_symb_bound                   200
% 2.26/0.99  --lt_threshold                          2000
% 2.26/0.99  --clause_weak_htbl                      true
% 2.26/0.99  --gc_record_bc_elim                     false
% 2.26/0.99  
% 2.26/0.99  ------ Preprocessing Options
% 2.26/0.99  
% 2.26/0.99  --preprocessing_flag                    true
% 2.26/0.99  --time_out_prep_mult                    0.1
% 2.26/0.99  --splitting_mode                        input
% 2.26/0.99  --splitting_grd                         true
% 2.26/0.99  --splitting_cvd                         false
% 2.26/0.99  --splitting_cvd_svl                     false
% 2.26/0.99  --splitting_nvd                         32
% 2.26/0.99  --sub_typing                            true
% 2.26/0.99  --prep_gs_sim                           true
% 2.26/0.99  --prep_unflatten                        true
% 2.26/0.99  --prep_res_sim                          true
% 2.26/0.99  --prep_upred                            true
% 2.26/0.99  --prep_sem_filter                       exhaustive
% 2.26/0.99  --prep_sem_filter_out                   false
% 2.26/0.99  --pred_elim                             true
% 2.26/0.99  --res_sim_input                         true
% 2.26/0.99  --eq_ax_congr_red                       true
% 2.26/0.99  --pure_diseq_elim                       true
% 2.26/0.99  --brand_transform                       false
% 2.26/0.99  --non_eq_to_eq                          false
% 2.26/0.99  --prep_def_merge                        true
% 2.26/0.99  --prep_def_merge_prop_impl              false
% 2.26/0.99  --prep_def_merge_mbd                    true
% 2.26/0.99  --prep_def_merge_tr_red                 false
% 2.26/0.99  --prep_def_merge_tr_cl                  false
% 2.26/0.99  --smt_preprocessing                     true
% 2.26/0.99  --smt_ac_axioms                         fast
% 2.26/0.99  --preprocessed_out                      false
% 2.26/0.99  --preprocessed_stats                    false
% 2.26/0.99  
% 2.26/0.99  ------ Abstraction refinement Options
% 2.26/0.99  
% 2.26/0.99  --abstr_ref                             []
% 2.26/0.99  --abstr_ref_prep                        false
% 2.26/0.99  --abstr_ref_until_sat                   false
% 2.26/0.99  --abstr_ref_sig_restrict                funpre
% 2.26/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.26/0.99  --abstr_ref_under                       []
% 2.26/0.99  
% 2.26/0.99  ------ SAT Options
% 2.26/0.99  
% 2.26/0.99  --sat_mode                              false
% 2.26/0.99  --sat_fm_restart_options                ""
% 2.26/0.99  --sat_gr_def                            false
% 2.26/0.99  --sat_epr_types                         true
% 2.26/0.99  --sat_non_cyclic_types                  false
% 2.26/0.99  --sat_finite_models                     false
% 2.26/0.99  --sat_fm_lemmas                         false
% 2.26/0.99  --sat_fm_prep                           false
% 2.26/0.99  --sat_fm_uc_incr                        true
% 2.26/0.99  --sat_out_model                         small
% 2.26/0.99  --sat_out_clauses                       false
% 2.26/0.99  
% 2.26/0.99  ------ QBF Options
% 2.26/0.99  
% 2.26/0.99  --qbf_mode                              false
% 2.26/0.99  --qbf_elim_univ                         false
% 2.26/0.99  --qbf_dom_inst                          none
% 2.26/0.99  --qbf_dom_pre_inst                      false
% 2.26/0.99  --qbf_sk_in                             false
% 2.26/0.99  --qbf_pred_elim                         true
% 2.26/0.99  --qbf_split                             512
% 2.26/0.99  
% 2.26/0.99  ------ BMC1 Options
% 2.26/0.99  
% 2.26/0.99  --bmc1_incremental                      false
% 2.26/0.99  --bmc1_axioms                           reachable_all
% 2.26/0.99  --bmc1_min_bound                        0
% 2.26/0.99  --bmc1_max_bound                        -1
% 2.26/0.99  --bmc1_max_bound_default                -1
% 2.26/0.99  --bmc1_symbol_reachability              true
% 2.26/0.99  --bmc1_property_lemmas                  false
% 2.26/0.99  --bmc1_k_induction                      false
% 2.26/0.99  --bmc1_non_equiv_states                 false
% 2.26/0.99  --bmc1_deadlock                         false
% 2.26/0.99  --bmc1_ucm                              false
% 2.26/0.99  --bmc1_add_unsat_core                   none
% 2.26/0.99  --bmc1_unsat_core_children              false
% 2.26/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.26/0.99  --bmc1_out_stat                         full
% 2.26/0.99  --bmc1_ground_init                      false
% 2.26/0.99  --bmc1_pre_inst_next_state              false
% 2.26/0.99  --bmc1_pre_inst_state                   false
% 2.26/0.99  --bmc1_pre_inst_reach_state             false
% 2.26/0.99  --bmc1_out_unsat_core                   false
% 2.26/0.99  --bmc1_aig_witness_out                  false
% 2.26/0.99  --bmc1_verbose                          false
% 2.26/0.99  --bmc1_dump_clauses_tptp                false
% 2.26/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.26/0.99  --bmc1_dump_file                        -
% 2.26/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.26/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.26/0.99  --bmc1_ucm_extend_mode                  1
% 2.26/0.99  --bmc1_ucm_init_mode                    2
% 2.26/0.99  --bmc1_ucm_cone_mode                    none
% 2.26/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.26/0.99  --bmc1_ucm_relax_model                  4
% 2.26/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.26/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.26/0.99  --bmc1_ucm_layered_model                none
% 2.26/0.99  --bmc1_ucm_max_lemma_size               10
% 2.26/0.99  
% 2.26/0.99  ------ AIG Options
% 2.26/0.99  
% 2.26/0.99  --aig_mode                              false
% 2.26/0.99  
% 2.26/0.99  ------ Instantiation Options
% 2.26/0.99  
% 2.26/0.99  --instantiation_flag                    true
% 2.26/0.99  --inst_sos_flag                         false
% 2.26/0.99  --inst_sos_phase                        true
% 2.26/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.26/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.26/0.99  --inst_lit_sel_side                     none
% 2.26/0.99  --inst_solver_per_active                1400
% 2.26/0.99  --inst_solver_calls_frac                1.
% 2.26/0.99  --inst_passive_queue_type               priority_queues
% 2.26/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.26/0.99  --inst_passive_queues_freq              [25;2]
% 2.26/0.99  --inst_dismatching                      true
% 2.26/0.99  --inst_eager_unprocessed_to_passive     true
% 2.26/0.99  --inst_prop_sim_given                   true
% 2.26/0.99  --inst_prop_sim_new                     false
% 2.26/0.99  --inst_subs_new                         false
% 2.26/0.99  --inst_eq_res_simp                      false
% 2.26/0.99  --inst_subs_given                       false
% 2.26/0.99  --inst_orphan_elimination               true
% 2.26/0.99  --inst_learning_loop_flag               true
% 2.26/0.99  --inst_learning_start                   3000
% 2.26/0.99  --inst_learning_factor                  2
% 2.26/0.99  --inst_start_prop_sim_after_learn       3
% 2.26/0.99  --inst_sel_renew                        solver
% 2.26/0.99  --inst_lit_activity_flag                true
% 2.26/0.99  --inst_restr_to_given                   false
% 2.26/0.99  --inst_activity_threshold               500
% 2.26/0.99  --inst_out_proof                        true
% 2.26/0.99  
% 2.26/0.99  ------ Resolution Options
% 2.26/0.99  
% 2.26/0.99  --resolution_flag                       false
% 2.26/0.99  --res_lit_sel                           adaptive
% 2.26/0.99  --res_lit_sel_side                      none
% 2.26/0.99  --res_ordering                          kbo
% 2.26/0.99  --res_to_prop_solver                    active
% 2.26/0.99  --res_prop_simpl_new                    false
% 2.26/0.99  --res_prop_simpl_given                  true
% 2.26/0.99  --res_passive_queue_type                priority_queues
% 2.26/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.26/0.99  --res_passive_queues_freq               [15;5]
% 2.26/0.99  --res_forward_subs                      full
% 2.26/0.99  --res_backward_subs                     full
% 2.26/0.99  --res_forward_subs_resolution           true
% 2.26/0.99  --res_backward_subs_resolution          true
% 2.26/0.99  --res_orphan_elimination                true
% 2.26/0.99  --res_time_limit                        2.
% 2.26/0.99  --res_out_proof                         true
% 2.26/0.99  
% 2.26/0.99  ------ Superposition Options
% 2.26/0.99  
% 2.26/0.99  --superposition_flag                    true
% 2.26/0.99  --sup_passive_queue_type                priority_queues
% 2.26/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.26/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.26/0.99  --demod_completeness_check              fast
% 2.26/0.99  --demod_use_ground                      true
% 2.26/0.99  --sup_to_prop_solver                    passive
% 2.26/0.99  --sup_prop_simpl_new                    true
% 2.26/0.99  --sup_prop_simpl_given                  true
% 2.26/0.99  --sup_fun_splitting                     false
% 2.26/0.99  --sup_smt_interval                      50000
% 2.26/0.99  
% 2.26/0.99  ------ Superposition Simplification Setup
% 2.26/0.99  
% 2.26/0.99  --sup_indices_passive                   []
% 2.26/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.26/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.26/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.26/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.26/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.26/0.99  --sup_full_bw                           [BwDemod]
% 2.26/0.99  --sup_immed_triv                        [TrivRules]
% 2.26/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.26/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.26/0.99  --sup_immed_bw_main                     []
% 2.26/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.26/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.26/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.26/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.26/0.99  
% 2.26/0.99  ------ Combination Options
% 2.26/0.99  
% 2.26/0.99  --comb_res_mult                         3
% 2.26/0.99  --comb_sup_mult                         2
% 2.26/0.99  --comb_inst_mult                        10
% 2.26/0.99  
% 2.26/0.99  ------ Debug Options
% 2.26/0.99  
% 2.26/0.99  --dbg_backtrace                         false
% 2.26/0.99  --dbg_dump_prop_clauses                 false
% 2.26/0.99  --dbg_dump_prop_clauses_file            -
% 2.26/0.99  --dbg_out_stat                          false
% 2.26/0.99  
% 2.26/0.99  
% 2.26/0.99  
% 2.26/0.99  
% 2.26/0.99  ------ Proving...
% 2.26/0.99  
% 2.26/0.99  
% 2.26/0.99  % SZS status Theorem for theBenchmark.p
% 2.26/0.99  
% 2.26/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.26/0.99  
% 2.26/0.99  fof(f9,conjecture,(
% 2.26/0.99    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1)))),
% 2.26/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.26/0.99  
% 2.26/0.99  fof(f10,negated_conjecture,(
% 2.26/0.99    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1)))),
% 2.26/0.99    inference(negated_conjecture,[],[f9])).
% 2.26/0.99  
% 2.26/0.99  fof(f27,plain,(
% 2.26/0.99    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)))),
% 2.26/0.99    inference(ennf_transformation,[],[f10])).
% 2.26/0.99  
% 2.26/0.99  fof(f28,plain,(
% 2.26/0.99    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 2.26/0.99    inference(flattening,[],[f27])).
% 2.26/0.99  
% 2.26/0.99  fof(f42,plain,(
% 2.26/0.99    ( ! [X0,X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) => (k12_lattice3(X0,X1,k13_lattice3(X0,X1,sK4)) != X1 & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 2.26/0.99    introduced(choice_axiom,[])).
% 2.26/0.99  
% 2.26/0.99  fof(f41,plain,(
% 2.26/0.99    ( ! [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k12_lattice3(X0,sK3,k13_lattice3(X0,sK3,X2)) != sK3 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 2.26/0.99    introduced(choice_axiom,[])).
% 2.26/0.99  
% 2.26/0.99  fof(f40,plain,(
% 2.26/0.99    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => (? [X1] : (? [X2] : (k12_lattice3(sK2,X1,k13_lattice3(sK2,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_orders_2(sK2) & v2_lattice3(sK2) & v1_lattice3(sK2) & v5_orders_2(sK2) & v3_orders_2(sK2))),
% 2.26/0.99    introduced(choice_axiom,[])).
% 2.26/0.99  
% 2.26/0.99  fof(f43,plain,(
% 2.26/0.99    ((k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 & m1_subset_1(sK4,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_orders_2(sK2) & v2_lattice3(sK2) & v1_lattice3(sK2) & v5_orders_2(sK2) & v3_orders_2(sK2)),
% 2.26/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f28,f42,f41,f40])).
% 2.26/0.99  
% 2.26/0.99  fof(f71,plain,(
% 2.26/0.99    m1_subset_1(sK4,u1_struct_0(sK2))),
% 2.26/0.99    inference(cnf_transformation,[],[f43])).
% 2.26/0.99  
% 2.26/0.99  fof(f70,plain,(
% 2.26/0.99    m1_subset_1(sK3,u1_struct_0(sK2))),
% 2.26/0.99    inference(cnf_transformation,[],[f43])).
% 2.26/0.99  
% 2.26/0.99  fof(f8,axiom,(
% 2.26/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2))),
% 2.26/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.26/0.99  
% 2.26/0.99  fof(f25,plain,(
% 2.26/0.99    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 2.26/0.99    inference(ennf_transformation,[],[f8])).
% 2.26/0.99  
% 2.26/0.99  fof(f26,plain,(
% 2.26/0.99    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 2.26/0.99    inference(flattening,[],[f25])).
% 2.26/0.99  
% 2.26/0.99  fof(f64,plain,(
% 2.26/0.99    ( ! [X2,X0,X1] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 2.26/0.99    inference(cnf_transformation,[],[f26])).
% 2.26/0.99  
% 2.26/0.99  fof(f67,plain,(
% 2.26/0.99    v1_lattice3(sK2)),
% 2.26/0.99    inference(cnf_transformation,[],[f43])).
% 2.26/0.99  
% 2.26/0.99  fof(f66,plain,(
% 2.26/0.99    v5_orders_2(sK2)),
% 2.26/0.99    inference(cnf_transformation,[],[f43])).
% 2.26/0.99  
% 2.26/0.99  fof(f69,plain,(
% 2.26/0.99    l1_orders_2(sK2)),
% 2.26/0.99    inference(cnf_transformation,[],[f43])).
% 2.26/0.99  
% 2.26/0.99  fof(f5,axiom,(
% 2.26/0.99    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 2.26/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.26/0.99  
% 2.26/0.99  fof(f19,plain,(
% 2.26/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 2.26/0.99    inference(ennf_transformation,[],[f5])).
% 2.26/0.99  
% 2.26/0.99  fof(f20,plain,(
% 2.26/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.26/0.99    inference(flattening,[],[f19])).
% 2.26/0.99  
% 2.26/0.99  fof(f30,plain,(
% 2.26/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3))) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.26/0.99    inference(nnf_transformation,[],[f20])).
% 2.26/0.99  
% 2.26/0.99  fof(f31,plain,(
% 2.26/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.26/0.99    inference(flattening,[],[f30])).
% 2.26/0.99  
% 2.26/0.99  fof(f32,plain,(
% 2.26/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.26/0.99    inference(rectify,[],[f31])).
% 2.26/0.99  
% 2.26/0.99  fof(f33,plain,(
% 2.26/0.99    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,X3,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))))),
% 2.26/0.99    introduced(choice_axiom,[])).
% 2.26/0.99  
% 2.26/0.99  fof(f34,plain,(
% 2.26/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,X3,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.26/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 2.26/0.99  
% 2.26/0.99  fof(f49,plain,(
% 2.26/0.99    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X1,X3) | k10_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.26/0.99    inference(cnf_transformation,[],[f34])).
% 2.26/0.99  
% 2.26/0.99  fof(f75,plain,(
% 2.26/0.99    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.26/0.99    inference(equality_resolution,[],[f49])).
% 2.26/0.99  
% 2.26/0.99  fof(f3,axiom,(
% 2.26/0.99    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 2.26/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.26/0.99  
% 2.26/0.99  fof(f15,plain,(
% 2.26/0.99    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 2.26/0.99    inference(ennf_transformation,[],[f3])).
% 2.26/0.99  
% 2.26/0.99  fof(f16,plain,(
% 2.26/0.99    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 2.26/0.99    inference(flattening,[],[f15])).
% 2.26/0.99  
% 2.26/0.99  fof(f47,plain,(
% 2.26/0.99    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 2.26/0.99    inference(cnf_transformation,[],[f16])).
% 2.26/0.99  
% 2.26/0.99  fof(f6,axiom,(
% 2.26/0.99    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 2.26/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.26/0.99  
% 2.26/0.99  fof(f21,plain,(
% 2.26/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 2.26/0.99    inference(ennf_transformation,[],[f6])).
% 2.26/0.99  
% 2.26/0.99  fof(f22,plain,(
% 2.26/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.26/0.99    inference(flattening,[],[f21])).
% 2.26/0.99  
% 2.26/0.99  fof(f35,plain,(
% 2.26/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.26/0.99    inference(nnf_transformation,[],[f22])).
% 2.26/0.99  
% 2.26/0.99  fof(f36,plain,(
% 2.26/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.26/0.99    inference(flattening,[],[f35])).
% 2.26/0.99  
% 2.26/0.99  fof(f37,plain,(
% 2.26/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.26/0.99    inference(rectify,[],[f36])).
% 2.26/0.99  
% 2.26/0.99  fof(f38,plain,(
% 2.26/0.99    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK1(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X1) & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0))))),
% 2.26/0.99    introduced(choice_axiom,[])).
% 2.26/0.99  
% 2.26/0.99  fof(f39,plain,(
% 2.26/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,sK1(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X1) & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.26/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).
% 2.26/0.99  
% 2.26/0.99  fof(f60,plain,(
% 2.26/0.99    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | r1_orders_2(X0,sK1(X0,X1,X2,X3),X1) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.26/0.99    inference(cnf_transformation,[],[f39])).
% 2.26/0.99  
% 2.26/0.99  fof(f68,plain,(
% 2.26/0.99    v2_lattice3(sK2)),
% 2.26/0.99    inference(cnf_transformation,[],[f43])).
% 2.26/0.99  
% 2.26/0.99  fof(f62,plain,(
% 2.26/0.99    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,sK1(X0,X1,X2,X3),X3) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.26/0.99    inference(cnf_transformation,[],[f39])).
% 2.26/0.99  
% 2.26/0.99  fof(f4,axiom,(
% 2.26/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 2.26/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.26/0.99  
% 2.26/0.99  fof(f17,plain,(
% 2.26/0.99    ! [X0,X1,X2] : (m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 2.26/0.99    inference(ennf_transformation,[],[f4])).
% 2.26/0.99  
% 2.26/0.99  fof(f18,plain,(
% 2.26/0.99    ! [X0,X1,X2] : (m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 2.26/0.99    inference(flattening,[],[f17])).
% 2.26/0.99  
% 2.26/0.99  fof(f48,plain,(
% 2.26/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 2.26/0.99    inference(cnf_transformation,[],[f18])).
% 2.26/0.99  
% 2.26/0.99  fof(f7,axiom,(
% 2.26/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2))),
% 2.26/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.26/0.99  
% 2.26/0.99  fof(f23,plain,(
% 2.26/0.99    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 2.26/0.99    inference(ennf_transformation,[],[f7])).
% 2.26/0.99  
% 2.26/0.99  fof(f24,plain,(
% 2.26/0.99    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 2.26/0.99    inference(flattening,[],[f23])).
% 2.26/0.99  
% 2.26/0.99  fof(f63,plain,(
% 2.26/0.99    ( ! [X2,X0,X1] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 2.26/0.99    inference(cnf_transformation,[],[f24])).
% 2.26/0.99  
% 2.26/0.99  fof(f2,axiom,(
% 2.26/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => r3_orders_2(X0,X1,X1))),
% 2.26/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.26/0.99  
% 2.26/0.99  fof(f13,plain,(
% 2.26/0.99    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.26/0.99    inference(ennf_transformation,[],[f2])).
% 2.26/0.99  
% 2.26/0.99  fof(f14,plain,(
% 2.26/0.99    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.26/0.99    inference(flattening,[],[f13])).
% 2.26/0.99  
% 2.26/0.99  fof(f46,plain,(
% 2.26/0.99    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.26/0.99    inference(cnf_transformation,[],[f14])).
% 2.26/0.99  
% 2.26/0.99  fof(f65,plain,(
% 2.26/0.99    v3_orders_2(sK2)),
% 2.26/0.99    inference(cnf_transformation,[],[f43])).
% 2.26/0.99  
% 2.26/0.99  fof(f1,axiom,(
% 2.26/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 2.26/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.26/0.99  
% 2.26/0.99  fof(f11,plain,(
% 2.26/0.99    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.26/0.99    inference(ennf_transformation,[],[f1])).
% 2.26/0.99  
% 2.26/0.99  fof(f12,plain,(
% 2.26/0.99    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.26/0.99    inference(flattening,[],[f11])).
% 2.26/0.99  
% 2.26/0.99  fof(f29,plain,(
% 2.26/0.99    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.26/0.99    inference(nnf_transformation,[],[f12])).
% 2.26/0.99  
% 2.26/0.99  fof(f44,plain,(
% 2.26/0.99    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.26/0.99    inference(cnf_transformation,[],[f29])).
% 2.26/0.99  
% 2.26/0.99  fof(f72,plain,(
% 2.26/0.99    k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3),
% 2.26/0.99    inference(cnf_transformation,[],[f43])).
% 2.26/0.99  
% 2.26/0.99  cnf(c_22,negated_conjecture,
% 2.26/0.99      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 2.26/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1190,negated_conjecture,
% 2.26/0.99      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 2.26/0.99      inference(subtyping,[status(esa)],[c_22]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1572,plain,
% 2.26/0.99      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 2.26/0.99      inference(predicate_to_equality,[status(thm)],[c_1190]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_23,negated_conjecture,
% 2.26/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.26/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1189,negated_conjecture,
% 2.26/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.26/0.99      inference(subtyping,[status(esa)],[c_23]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1573,plain,
% 2.26/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 2.26/0.99      inference(predicate_to_equality,[status(thm)],[c_1189]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_20,plain,
% 2.26/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.26/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.26/0.99      | ~ v5_orders_2(X1)
% 2.26/0.99      | ~ v1_lattice3(X1)
% 2.26/0.99      | ~ l1_orders_2(X1)
% 2.26/0.99      | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0) ),
% 2.26/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_26,negated_conjecture,
% 2.26/0.99      ( v1_lattice3(sK2) ),
% 2.26/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_657,plain,
% 2.26/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.26/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.26/0.99      | ~ v5_orders_2(X1)
% 2.26/0.99      | ~ l1_orders_2(X1)
% 2.26/0.99      | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0)
% 2.26/0.99      | sK2 != X1 ),
% 2.26/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_26]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_658,plain,
% 2.26/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.26/0.99      | ~ v5_orders_2(sK2)
% 2.26/0.99      | ~ l1_orders_2(sK2)
% 2.26/0.99      | k10_lattice3(sK2,X0,X1) = k13_lattice3(sK2,X0,X1) ),
% 2.26/0.99      inference(unflattening,[status(thm)],[c_657]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_27,negated_conjecture,
% 2.26/0.99      ( v5_orders_2(sK2) ),
% 2.26/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_24,negated_conjecture,
% 2.26/0.99      ( l1_orders_2(sK2) ),
% 2.26/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_662,plain,
% 2.26/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.26/0.99      | k10_lattice3(sK2,X0,X1) = k13_lattice3(sK2,X0,X1) ),
% 2.26/0.99      inference(global_propositional_subsumption,
% 2.26/0.99                [status(thm)],
% 2.26/0.99                [c_658,c_27,c_24]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_663,plain,
% 2.26/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.26/0.99      | k10_lattice3(sK2,X1,X0) = k13_lattice3(sK2,X1,X0) ),
% 2.26/0.99      inference(renaming,[status(thm)],[c_662]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1180,plain,
% 2.26/0.99      ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 2.26/0.99      | k10_lattice3(sK2,X1_47,X0_47) = k13_lattice3(sK2,X1_47,X0_47) ),
% 2.26/0.99      inference(subtyping,[status(esa)],[c_663]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1584,plain,
% 2.26/0.99      ( k10_lattice3(sK2,X0_47,X1_47) = k13_lattice3(sK2,X0_47,X1_47)
% 2.26/0.99      | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top
% 2.26/0.99      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
% 2.26/0.99      inference(predicate_to_equality,[status(thm)],[c_1180]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1858,plain,
% 2.26/0.99      ( k10_lattice3(sK2,sK3,X0_47) = k13_lattice3(sK2,sK3,X0_47)
% 2.26/0.99      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
% 2.26/0.99      inference(superposition,[status(thm)],[c_1573,c_1584]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1985,plain,
% 2.26/0.99      ( k10_lattice3(sK2,sK3,sK4) = k13_lattice3(sK2,sK3,sK4) ),
% 2.26/0.99      inference(superposition,[status(thm)],[c_1572,c_1858]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_11,plain,
% 2.26/0.99      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 2.26/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.26/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.26/0.99      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.26/0.99      | ~ v5_orders_2(X0)
% 2.26/0.99      | ~ v1_lattice3(X0)
% 2.26/0.99      | v2_struct_0(X0)
% 2.26/0.99      | ~ l1_orders_2(X0) ),
% 2.26/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_3,plain,
% 2.26/0.99      ( ~ v1_lattice3(X0) | ~ v2_struct_0(X0) | ~ l1_orders_2(X0) ),
% 2.26/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_164,plain,
% 2.26/0.99      ( ~ v1_lattice3(X0)
% 2.26/0.99      | ~ v5_orders_2(X0)
% 2.26/0.99      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.26/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.26/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.26/0.99      | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 2.26/0.99      | ~ l1_orders_2(X0) ),
% 2.26/0.99      inference(global_propositional_subsumption,
% 2.26/0.99                [status(thm)],
% 2.26/0.99                [c_11,c_3]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_165,plain,
% 2.26/0.99      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 2.26/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.26/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.26/0.99      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.26/0.99      | ~ v5_orders_2(X0)
% 2.26/0.99      | ~ v1_lattice3(X0)
% 2.26/0.99      | ~ l1_orders_2(X0) ),
% 2.26/0.99      inference(renaming,[status(thm)],[c_164]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_626,plain,
% 2.26/0.99      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 2.26/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.26/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.26/0.99      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.26/0.99      | ~ v5_orders_2(X0)
% 2.26/0.99      | ~ l1_orders_2(X0)
% 2.26/0.99      | sK2 != X0 ),
% 2.26/0.99      inference(resolution_lifted,[status(thm)],[c_165,c_26]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_627,plain,
% 2.26/0.99      ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
% 2.26/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2))
% 2.26/0.99      | ~ v5_orders_2(sK2)
% 2.26/0.99      | ~ l1_orders_2(sK2) ),
% 2.26/0.99      inference(unflattening,[status(thm)],[c_626]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_629,plain,
% 2.26/0.99      ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
% 2.26/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
% 2.26/0.99      inference(global_propositional_subsumption,
% 2.26/0.99                [status(thm)],
% 2.26/0.99                [c_627,c_27,c_24]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_630,plain,
% 2.26/0.99      ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
% 2.26/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
% 2.26/0.99      inference(renaming,[status(thm)],[c_629]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1181,plain,
% 2.26/0.99      ( r1_orders_2(sK2,X0_47,k10_lattice3(sK2,X0_47,X1_47))
% 2.26/0.99      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(k10_lattice3(sK2,X0_47,X1_47),u1_struct_0(sK2)) ),
% 2.26/0.99      inference(subtyping,[status(esa)],[c_630]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1583,plain,
% 2.26/0.99      ( r1_orders_2(sK2,X0_47,k10_lattice3(sK2,X0_47,X1_47)) = iProver_top
% 2.26/0.99      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 2.26/0.99      | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top
% 2.26/0.99      | m1_subset_1(k10_lattice3(sK2,X0_47,X1_47),u1_struct_0(sK2)) != iProver_top ),
% 2.26/0.99      inference(predicate_to_equality,[status(thm)],[c_1181]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_3205,plain,
% 2.26/0.99      ( r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK4)) = iProver_top
% 2.26/0.99      | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 2.26/0.99      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 2.26/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 2.26/0.99      inference(superposition,[status(thm)],[c_1985,c_1583]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_3250,plain,
% 2.26/0.99      ( r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = iProver_top
% 2.26/0.99      | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 2.26/0.99      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 2.26/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 2.26/0.99      inference(light_normalisation,[status(thm)],[c_3205,c_1985]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_14,plain,
% 2.26/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 2.26/0.99      | ~ r1_orders_2(X0,X1,X3)
% 2.26/0.99      | r1_orders_2(X0,sK1(X0,X3,X2,X1),X3)
% 2.26/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.26/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.26/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.26/0.99      | ~ v2_lattice3(X0)
% 2.26/0.99      | ~ v5_orders_2(X0)
% 2.26/0.99      | v2_struct_0(X0)
% 2.26/0.99      | ~ l1_orders_2(X0)
% 2.26/0.99      | k11_lattice3(X0,X3,X2) = X1 ),
% 2.26/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_646,plain,
% 2.26/0.99      ( ~ v2_struct_0(X0) | ~ l1_orders_2(X0) | sK2 != X0 ),
% 2.26/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_26]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_647,plain,
% 2.26/0.99      ( ~ v2_struct_0(sK2) | ~ l1_orders_2(sK2) ),
% 2.26/0.99      inference(unflattening,[status(thm)],[c_646]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_80,plain,
% 2.26/0.99      ( ~ v1_lattice3(sK2) | ~ v2_struct_0(sK2) | ~ l1_orders_2(sK2) ),
% 2.26/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_649,plain,
% 2.26/0.99      ( ~ v2_struct_0(sK2) ),
% 2.26/0.99      inference(global_propositional_subsumption,
% 2.26/0.99                [status(thm)],
% 2.26/0.99                [c_647,c_26,c_24,c_80]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_869,plain,
% 2.26/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 2.26/0.99      | ~ r1_orders_2(X0,X1,X3)
% 2.26/0.99      | r1_orders_2(X0,sK1(X0,X3,X2,X1),X3)
% 2.26/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.26/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.26/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.26/0.99      | ~ v2_lattice3(X0)
% 2.26/0.99      | ~ v5_orders_2(X0)
% 2.26/0.99      | ~ l1_orders_2(X0)
% 2.26/0.99      | k11_lattice3(X0,X3,X2) = X1
% 2.26/0.99      | sK2 != X0 ),
% 2.26/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_649]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_870,plain,
% 2.26/0.99      ( ~ r1_orders_2(sK2,X0,X1)
% 2.26/0.99      | ~ r1_orders_2(sK2,X0,X2)
% 2.26/0.99      | r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X2)
% 2.26/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 2.26/0.99      | ~ v2_lattice3(sK2)
% 2.26/0.99      | ~ v5_orders_2(sK2)
% 2.26/0.99      | ~ l1_orders_2(sK2)
% 2.26/0.99      | k11_lattice3(sK2,X2,X1) = X0 ),
% 2.26/0.99      inference(unflattening,[status(thm)],[c_869]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_25,negated_conjecture,
% 2.26/0.99      ( v2_lattice3(sK2) ),
% 2.26/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_874,plain,
% 2.26/0.99      ( ~ m1_subset_1(X2,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.26/0.99      | r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X2)
% 2.26/0.99      | ~ r1_orders_2(sK2,X0,X2)
% 2.26/0.99      | ~ r1_orders_2(sK2,X0,X1)
% 2.26/0.99      | k11_lattice3(sK2,X2,X1) = X0 ),
% 2.26/0.99      inference(global_propositional_subsumption,
% 2.26/0.99                [status(thm)],
% 2.26/0.99                [c_870,c_27,c_25,c_24]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_875,plain,
% 2.26/0.99      ( ~ r1_orders_2(sK2,X0,X1)
% 2.26/0.99      | ~ r1_orders_2(sK2,X0,X2)
% 2.26/0.99      | r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X2)
% 2.26/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.26/0.99      | k11_lattice3(sK2,X2,X1) = X0 ),
% 2.26/0.99      inference(renaming,[status(thm)],[c_874]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1174,plain,
% 2.26/0.99      ( ~ r1_orders_2(sK2,X0_47,X1_47)
% 2.26/0.99      | ~ r1_orders_2(sK2,X0_47,X2_47)
% 2.26/0.99      | r1_orders_2(sK2,sK1(sK2,X2_47,X1_47,X0_47),X2_47)
% 2.26/0.99      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X2_47,u1_struct_0(sK2))
% 2.26/0.99      | k11_lattice3(sK2,X2_47,X1_47) = X0_47 ),
% 2.26/0.99      inference(subtyping,[status(esa)],[c_875]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_2032,plain,
% 2.26/0.99      ( ~ r1_orders_2(sK2,X0_47,k13_lattice3(sK2,sK3,sK4))
% 2.26/0.99      | ~ r1_orders_2(sK2,X0_47,sK3)
% 2.26/0.99      | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_47),sK3)
% 2.26/0.99      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.26/0.99      | k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_47 ),
% 2.26/0.99      inference(instantiation,[status(thm)],[c_1174]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_2048,plain,
% 2.26/0.99      ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_47
% 2.26/0.99      | r1_orders_2(sK2,X0_47,k13_lattice3(sK2,sK3,sK4)) != iProver_top
% 2.26/0.99      | r1_orders_2(sK2,X0_47,sK3) != iProver_top
% 2.26/0.99      | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_47),sK3) = iProver_top
% 2.26/0.99      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 2.26/0.99      | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 2.26/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 2.26/0.99      inference(predicate_to_equality,[status(thm)],[c_2032]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_2050,plain,
% 2.26/0.99      ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
% 2.26/0.99      | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),sK3),sK3) = iProver_top
% 2.26/0.99      | r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != iProver_top
% 2.26/0.99      | r1_orders_2(sK2,sK3,sK3) != iProver_top
% 2.26/0.99      | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 2.26/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 2.26/0.99      inference(instantiation,[status(thm)],[c_2048]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_12,plain,
% 2.26/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 2.26/0.99      | ~ r1_orders_2(X0,X1,X3)
% 2.26/0.99      | ~ r1_orders_2(X0,sK1(X0,X3,X2,X1),X1)
% 2.26/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.26/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.26/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.26/0.99      | ~ v2_lattice3(X0)
% 2.26/0.99      | ~ v5_orders_2(X0)
% 2.26/0.99      | v2_struct_0(X0)
% 2.26/0.99      | ~ l1_orders_2(X0)
% 2.26/0.99      | k11_lattice3(X0,X3,X2) = X1 ),
% 2.26/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_931,plain,
% 2.26/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 2.26/0.99      | ~ r1_orders_2(X0,X1,X3)
% 2.26/0.99      | ~ r1_orders_2(X0,sK1(X0,X3,X2,X1),X1)
% 2.26/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.26/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.26/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.26/0.99      | ~ v2_lattice3(X0)
% 2.26/0.99      | ~ v5_orders_2(X0)
% 2.26/0.99      | ~ l1_orders_2(X0)
% 2.26/0.99      | k11_lattice3(X0,X3,X2) = X1
% 2.26/0.99      | sK2 != X0 ),
% 2.26/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_649]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_932,plain,
% 2.26/0.99      ( ~ r1_orders_2(sK2,X0,X1)
% 2.26/0.99      | ~ r1_orders_2(sK2,X0,X2)
% 2.26/0.99      | ~ r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X0)
% 2.26/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 2.26/0.99      | ~ v2_lattice3(sK2)
% 2.26/0.99      | ~ v5_orders_2(sK2)
% 2.26/0.99      | ~ l1_orders_2(sK2)
% 2.26/0.99      | k11_lattice3(sK2,X2,X1) = X0 ),
% 2.26/0.99      inference(unflattening,[status(thm)],[c_931]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_936,plain,
% 2.26/0.99      ( ~ m1_subset_1(X2,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.26/0.99      | ~ r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X0)
% 2.26/0.99      | ~ r1_orders_2(sK2,X0,X2)
% 2.26/0.99      | ~ r1_orders_2(sK2,X0,X1)
% 2.26/0.99      | k11_lattice3(sK2,X2,X1) = X0 ),
% 2.26/0.99      inference(global_propositional_subsumption,
% 2.26/0.99                [status(thm)],
% 2.26/0.99                [c_932,c_27,c_25,c_24]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_937,plain,
% 2.26/0.99      ( ~ r1_orders_2(sK2,X0,X1)
% 2.26/0.99      | ~ r1_orders_2(sK2,X0,X2)
% 2.26/0.99      | ~ r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X0)
% 2.26/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.26/0.99      | k11_lattice3(sK2,X2,X1) = X0 ),
% 2.26/0.99      inference(renaming,[status(thm)],[c_936]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1172,plain,
% 2.26/0.99      ( ~ r1_orders_2(sK2,X0_47,X1_47)
% 2.26/0.99      | ~ r1_orders_2(sK2,X0_47,X2_47)
% 2.26/0.99      | ~ r1_orders_2(sK2,sK1(sK2,X2_47,X1_47,X0_47),X0_47)
% 2.26/0.99      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X2_47,u1_struct_0(sK2))
% 2.26/0.99      | k11_lattice3(sK2,X2_47,X1_47) = X0_47 ),
% 2.26/0.99      inference(subtyping,[status(esa)],[c_937]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_2034,plain,
% 2.26/0.99      ( ~ r1_orders_2(sK2,X0_47,k13_lattice3(sK2,sK3,sK4))
% 2.26/0.99      | ~ r1_orders_2(sK2,X0_47,sK3)
% 2.26/0.99      | ~ r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_47),X0_47)
% 2.26/0.99      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.26/0.99      | k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_47 ),
% 2.26/0.99      inference(instantiation,[status(thm)],[c_1172]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_2040,plain,
% 2.26/0.99      ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_47
% 2.26/0.99      | r1_orders_2(sK2,X0_47,k13_lattice3(sK2,sK3,sK4)) != iProver_top
% 2.26/0.99      | r1_orders_2(sK2,X0_47,sK3) != iProver_top
% 2.26/0.99      | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_47),X0_47) != iProver_top
% 2.26/0.99      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 2.26/0.99      | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 2.26/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 2.26/0.99      inference(predicate_to_equality,[status(thm)],[c_2034]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_2042,plain,
% 2.26/0.99      ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
% 2.26/0.99      | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),sK3),sK3) != iProver_top
% 2.26/0.99      | r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != iProver_top
% 2.26/0.99      | r1_orders_2(sK2,sK3,sK3) != iProver_top
% 2.26/0.99      | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 2.26/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 2.26/0.99      inference(instantiation,[status(thm)],[c_2040]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_4,plain,
% 2.26/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.26/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.26/0.99      | m1_subset_1(k13_lattice3(X1,X2,X0),u1_struct_0(X1))
% 2.26/0.99      | ~ v5_orders_2(X1)
% 2.26/0.99      | ~ v1_lattice3(X1)
% 2.26/0.99      | ~ l1_orders_2(X1) ),
% 2.26/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_678,plain,
% 2.26/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.26/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.26/0.99      | m1_subset_1(k13_lattice3(X1,X2,X0),u1_struct_0(X1))
% 2.26/0.99      | ~ v5_orders_2(X1)
% 2.26/0.99      | ~ l1_orders_2(X1)
% 2.26/0.99      | sK2 != X1 ),
% 2.26/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_26]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_679,plain,
% 2.26/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.26/0.99      | m1_subset_1(k13_lattice3(sK2,X0,X1),u1_struct_0(sK2))
% 2.26/0.99      | ~ v5_orders_2(sK2)
% 2.26/0.99      | ~ l1_orders_2(sK2) ),
% 2.26/0.99      inference(unflattening,[status(thm)],[c_678]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_683,plain,
% 2.26/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.26/0.99      | m1_subset_1(k13_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
% 2.26/0.99      inference(global_propositional_subsumption,
% 2.26/0.99                [status(thm)],
% 2.26/0.99                [c_679,c_27,c_24]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_684,plain,
% 2.26/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.26/0.99      | m1_subset_1(k13_lattice3(sK2,X1,X0),u1_struct_0(sK2)) ),
% 2.26/0.99      inference(renaming,[status(thm)],[c_683]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1179,plain,
% 2.26/0.99      ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 2.26/0.99      | m1_subset_1(k13_lattice3(sK2,X1_47,X0_47),u1_struct_0(sK2)) ),
% 2.26/0.99      inference(subtyping,[status(esa)],[c_684]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1959,plain,
% 2.26/0.99      ( m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.26/0.99      inference(instantiation,[status(thm)],[c_1179]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1960,plain,
% 2.26/0.99      ( m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) = iProver_top
% 2.26/0.99      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 2.26/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 2.26/0.99      inference(predicate_to_equality,[status(thm)],[c_1959]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1197,plain,
% 2.26/0.99      ( X0_47 != X1_47 | X2_47 != X1_47 | X2_47 = X0_47 ),
% 2.26/0.99      theory(equality) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1946,plain,
% 2.26/0.99      ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != X0_47
% 2.26/0.99      | sK3 != X0_47
% 2.26/0.99      | sK3 = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
% 2.26/0.99      inference(instantiation,[status(thm)],[c_1197]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1947,plain,
% 2.26/0.99      ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3
% 2.26/0.99      | sK3 = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
% 2.26/0.99      | sK3 != sK3 ),
% 2.26/0.99      inference(instantiation,[status(thm)],[c_1946]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_19,plain,
% 2.26/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.26/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.26/0.99      | ~ v2_lattice3(X1)
% 2.26/0.99      | ~ v5_orders_2(X1)
% 2.26/0.99      | ~ l1_orders_2(X1)
% 2.26/0.99      | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0) ),
% 2.26/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1014,plain,
% 2.26/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.26/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.26/0.99      | ~ v2_lattice3(X1)
% 2.26/0.99      | ~ v5_orders_2(X1)
% 2.26/0.99      | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0)
% 2.26/0.99      | sK2 != X1 ),
% 2.26/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_24]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1015,plain,
% 2.26/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.26/0.99      | ~ v2_lattice3(sK2)
% 2.26/0.99      | ~ v5_orders_2(sK2)
% 2.26/0.99      | k12_lattice3(sK2,X0,X1) = k11_lattice3(sK2,X0,X1) ),
% 2.26/0.99      inference(unflattening,[status(thm)],[c_1014]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1019,plain,
% 2.26/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.26/0.99      | k12_lattice3(sK2,X0,X1) = k11_lattice3(sK2,X0,X1) ),
% 2.26/0.99      inference(global_propositional_subsumption,
% 2.26/0.99                [status(thm)],
% 2.26/0.99                [c_1015,c_27,c_25]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1020,plain,
% 2.26/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.26/0.99      | k12_lattice3(sK2,X1,X0) = k11_lattice3(sK2,X1,X0) ),
% 2.26/0.99      inference(renaming,[status(thm)],[c_1019]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1171,plain,
% 2.26/0.99      ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 2.26/0.99      | k12_lattice3(sK2,X1_47,X0_47) = k11_lattice3(sK2,X1_47,X0_47) ),
% 2.26/0.99      inference(subtyping,[status(esa)],[c_1020]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1882,plain,
% 2.26/0.99      ( ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.26/0.99      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
% 2.26/0.99      inference(instantiation,[status(thm)],[c_1171]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1871,plain,
% 2.26/0.99      ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != X0_47
% 2.26/0.99      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
% 2.26/0.99      | sK3 != X0_47 ),
% 2.26/0.99      inference(instantiation,[status(thm)],[c_1197]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1881,plain,
% 2.26/0.99      ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
% 2.26/0.99      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
% 2.26/0.99      | sK3 != k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
% 2.26/0.99      inference(instantiation,[status(thm)],[c_1871]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_2,plain,
% 2.26/0.99      ( r3_orders_2(X0,X1,X1)
% 2.26/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.26/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.26/0.99      | v2_struct_0(X0)
% 2.26/0.99      | ~ v3_orders_2(X0)
% 2.26/0.99      | ~ l1_orders_2(X0) ),
% 2.26/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_28,negated_conjecture,
% 2.26/0.99      ( v3_orders_2(sK2) ),
% 2.26/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_338,plain,
% 2.26/0.99      ( r3_orders_2(X0,X1,X1)
% 2.26/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.26/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.26/0.99      | v2_struct_0(X0)
% 2.26/0.99      | ~ l1_orders_2(X0)
% 2.26/0.99      | sK2 != X0 ),
% 2.26/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_28]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_339,plain,
% 2.26/0.99      ( r3_orders_2(sK2,X0,X0)
% 2.26/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.26/0.99      | v2_struct_0(sK2)
% 2.26/0.99      | ~ l1_orders_2(sK2) ),
% 2.26/0.99      inference(unflattening,[status(thm)],[c_338]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_343,plain,
% 2.26/0.99      ( r3_orders_2(sK2,X0,X0)
% 2.26/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 2.26/0.99      inference(global_propositional_subsumption,
% 2.26/0.99                [status(thm)],
% 2.26/0.99                [c_339,c_26,c_24,c_80]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_344,plain,
% 2.26/0.99      ( r3_orders_2(sK2,X0,X0)
% 2.26/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 2.26/0.99      inference(renaming,[status(thm)],[c_343]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1,plain,
% 2.26/0.99      ( r1_orders_2(X0,X1,X2)
% 2.26/0.99      | ~ r3_orders_2(X0,X1,X2)
% 2.26/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.26/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.26/0.99      | v2_struct_0(X0)
% 2.26/0.99      | ~ v3_orders_2(X0)
% 2.26/0.99      | ~ l1_orders_2(X0) ),
% 2.26/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_359,plain,
% 2.26/0.99      ( r1_orders_2(X0,X1,X2)
% 2.26/0.99      | ~ r3_orders_2(X0,X1,X2)
% 2.26/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.26/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.26/0.99      | v2_struct_0(X0)
% 2.26/0.99      | ~ l1_orders_2(X0)
% 2.26/0.99      | sK2 != X0 ),
% 2.26/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_28]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_360,plain,
% 2.26/0.99      ( r1_orders_2(sK2,X0,X1)
% 2.26/0.99      | ~ r3_orders_2(sK2,X0,X1)
% 2.26/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.26/0.99      | v2_struct_0(sK2)
% 2.26/0.99      | ~ l1_orders_2(sK2) ),
% 2.26/0.99      inference(unflattening,[status(thm)],[c_359]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_364,plain,
% 2.26/0.99      ( r1_orders_2(sK2,X0,X1)
% 2.26/0.99      | ~ r3_orders_2(sK2,X0,X1)
% 2.26/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 2.26/0.99      inference(global_propositional_subsumption,
% 2.26/0.99                [status(thm)],
% 2.26/0.99                [c_360,c_26,c_24,c_80]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_365,plain,
% 2.26/0.99      ( r1_orders_2(sK2,X0,X1)
% 2.26/0.99      | ~ r3_orders_2(sK2,X0,X1)
% 2.26/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 2.26/0.99      inference(renaming,[status(thm)],[c_364]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_422,plain,
% 2.26/0.99      ( r1_orders_2(sK2,X0,X1)
% 2.26/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.26/0.99      | X0 != X3
% 2.26/0.99      | X1 != X3
% 2.26/0.99      | sK2 != sK2 ),
% 2.26/0.99      inference(resolution_lifted,[status(thm)],[c_344,c_365]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_423,plain,
% 2.26/0.99      ( r1_orders_2(sK2,X0,X0)
% 2.26/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 2.26/0.99      inference(unflattening,[status(thm)],[c_422]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1188,plain,
% 2.26/0.99      ( r1_orders_2(sK2,X0_47,X0_47)
% 2.26/0.99      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 2.26/0.99      | ~ m1_subset_1(X1_47,u1_struct_0(sK2)) ),
% 2.26/0.99      inference(subtyping,[status(esa)],[c_423]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1192,plain,
% 2.26/0.99      ( ~ m1_subset_1(X0_47,u1_struct_0(sK2)) | ~ sP0_iProver_split ),
% 2.26/0.99      inference(splitting,
% 2.26/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.26/0.99                [c_1188]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1214,plain,
% 2.26/0.99      ( m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 2.26/0.99      | sP0_iProver_split != iProver_top ),
% 2.26/0.99      inference(predicate_to_equality,[status(thm)],[c_1192]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1216,plain,
% 2.26/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.26/0.99      | sP0_iProver_split != iProver_top ),
% 2.26/0.99      inference(instantiation,[status(thm)],[c_1214]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1193,plain,
% 2.26/0.99      ( r1_orders_2(sK2,X0_47,X0_47)
% 2.26/0.99      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 2.26/0.99      | ~ sP1_iProver_split ),
% 2.26/0.99      inference(splitting,
% 2.26/0.99                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.26/0.99                [c_1188]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1211,plain,
% 2.26/0.99      ( r1_orders_2(sK2,X0_47,X0_47) = iProver_top
% 2.26/0.99      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 2.26/0.99      | sP1_iProver_split != iProver_top ),
% 2.26/0.99      inference(predicate_to_equality,[status(thm)],[c_1193]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1213,plain,
% 2.26/0.99      ( r1_orders_2(sK2,sK3,sK3) = iProver_top
% 2.26/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.26/0.99      | sP1_iProver_split != iProver_top ),
% 2.26/0.99      inference(instantiation,[status(thm)],[c_1211]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1194,plain,
% 2.26/0.99      ( sP1_iProver_split | sP0_iProver_split ),
% 2.26/0.99      inference(splitting,
% 2.26/0.99                [splitting(split),new_symbols(definition,[])],
% 2.26/0.99                [c_1188]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1210,plain,
% 2.26/0.99      ( sP1_iProver_split = iProver_top
% 2.26/0.99      | sP0_iProver_split = iProver_top ),
% 2.26/0.99      inference(predicate_to_equality,[status(thm)],[c_1194]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_21,negated_conjecture,
% 2.26/0.99      ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
% 2.26/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1191,negated_conjecture,
% 2.26/0.99      ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
% 2.26/0.99      inference(subtyping,[status(esa)],[c_21]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1196,plain,( X0_47 = X0_47 ),theory(equality) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1207,plain,
% 2.26/0.99      ( sK3 = sK3 ),
% 2.26/0.99      inference(instantiation,[status(thm)],[c_1196]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_35,plain,
% 2.26/0.99      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 2.26/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_34,plain,
% 2.26/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 2.26/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(contradiction,plain,
% 2.26/0.99      ( $false ),
% 2.26/0.99      inference(minisat,
% 2.26/0.99                [status(thm)],
% 2.26/0.99                [c_3250,c_2050,c_2042,c_1960,c_1959,c_1947,c_1882,c_1881,
% 2.26/0.99                 c_1216,c_1213,c_1210,c_1191,c_1207,c_35,c_22,c_34,c_23]) ).
% 2.26/0.99  
% 2.26/0.99  
% 2.26/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.26/0.99  
% 2.26/0.99  ------                               Statistics
% 2.26/0.99  
% 2.26/0.99  ------ General
% 2.26/0.99  
% 2.26/0.99  abstr_ref_over_cycles:                  0
% 2.26/0.99  abstr_ref_under_cycles:                 0
% 2.26/0.99  gc_basic_clause_elim:                   0
% 2.26/0.99  forced_gc_time:                         0
% 2.26/0.99  parsing_time:                           0.013
% 2.26/0.99  unif_index_cands_time:                  0.
% 2.26/0.99  unif_index_add_time:                    0.
% 2.26/0.99  orderings_time:                         0.
% 2.26/0.99  out_proof_time:                         0.012
% 2.26/0.99  total_time:                             0.14
% 2.26/0.99  num_of_symbols:                         52
% 2.26/0.99  num_of_terms:                           2739
% 2.26/0.99  
% 2.26/0.99  ------ Preprocessing
% 2.26/0.99  
% 2.26/0.99  num_of_splits:                          2
% 2.26/0.99  num_of_split_atoms:                     2
% 2.26/0.99  num_of_reused_defs:                     0
% 2.26/0.99  num_eq_ax_congr_red:                    48
% 2.26/0.99  num_of_sem_filtered_clauses:            3
% 2.26/0.99  num_of_subtypes:                        3
% 2.26/0.99  monotx_restored_types:                  0
% 2.26/0.99  sat_num_of_epr_types:                   0
% 2.26/0.99  sat_num_of_non_cyclic_types:            0
% 2.26/0.99  sat_guarded_non_collapsed_types:        1
% 2.26/0.99  num_pure_diseq_elim:                    0
% 2.26/0.99  simp_replaced_by:                       0
% 2.26/0.99  res_preprocessed:                       107
% 2.26/0.99  prep_upred:                             0
% 2.26/0.99  prep_unflattend:                        23
% 2.26/0.99  smt_new_axioms:                         0
% 2.26/0.99  pred_elim_cands:                        2
% 2.26/0.99  pred_elim:                              7
% 2.26/0.99  pred_elim_cl:                           8
% 2.26/0.99  pred_elim_cycles:                       9
% 2.26/0.99  merged_defs:                            0
% 2.26/0.99  merged_defs_ncl:                        0
% 2.26/0.99  bin_hyper_res:                          0
% 2.26/0.99  prep_cycles:                            4
% 2.26/0.99  pred_elim_time:                         0.016
% 2.26/0.99  splitting_time:                         0.
% 2.26/0.99  sem_filter_time:                        0.
% 2.26/0.99  monotx_time:                            0.
% 2.26/0.99  subtype_inf_time:                       0.
% 2.26/0.99  
% 2.26/0.99  ------ Problem properties
% 2.26/0.99  
% 2.26/0.99  clauses:                                23
% 2.26/0.99  conjectures:                            3
% 2.26/0.99  epr:                                    1
% 2.26/0.99  horn:                                   16
% 2.26/0.99  ground:                                 4
% 2.26/0.99  unary:                                  3
% 2.26/0.99  binary:                                 2
% 2.26/0.99  lits:                                   105
% 2.26/0.99  lits_eq:                                11
% 2.26/0.99  fd_pure:                                0
% 2.26/0.99  fd_pseudo:                              0
% 2.26/0.99  fd_cond:                                0
% 2.26/0.99  fd_pseudo_cond:                         8
% 2.26/0.99  ac_symbols:                             0
% 2.26/0.99  
% 2.26/0.99  ------ Propositional Solver
% 2.26/0.99  
% 2.26/0.99  prop_solver_calls:                      27
% 2.26/0.99  prop_fast_solver_calls:                 1444
% 2.26/0.99  smt_solver_calls:                       0
% 2.26/0.99  smt_fast_solver_calls:                  0
% 2.26/0.99  prop_num_of_clauses:                    898
% 2.26/0.99  prop_preprocess_simplified:             3864
% 2.26/0.99  prop_fo_subsumed:                       60
% 2.26/0.99  prop_solver_time:                       0.
% 2.26/0.99  smt_solver_time:                        0.
% 2.26/0.99  smt_fast_solver_time:                   0.
% 2.26/0.99  prop_fast_solver_time:                  0.
% 2.26/0.99  prop_unsat_core_time:                   0.
% 2.26/0.99  
% 2.26/0.99  ------ QBF
% 2.26/0.99  
% 2.26/0.99  qbf_q_res:                              0
% 2.26/0.99  qbf_num_tautologies:                    0
% 2.26/0.99  qbf_prep_cycles:                        0
% 2.26/0.99  
% 2.26/0.99  ------ BMC1
% 2.26/0.99  
% 2.26/0.99  bmc1_current_bound:                     -1
% 2.26/0.99  bmc1_last_solved_bound:                 -1
% 2.26/0.99  bmc1_unsat_core_size:                   -1
% 2.26/0.99  bmc1_unsat_core_parents_size:           -1
% 2.26/0.99  bmc1_merge_next_fun:                    0
% 2.26/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.26/0.99  
% 2.26/0.99  ------ Instantiation
% 2.26/0.99  
% 2.26/0.99  inst_num_of_clauses:                    224
% 2.26/0.99  inst_num_in_passive:                    50
% 2.26/0.99  inst_num_in_active:                     144
% 2.26/0.99  inst_num_in_unprocessed:                30
% 2.26/0.99  inst_num_of_loops:                      160
% 2.26/0.99  inst_num_of_learning_restarts:          0
% 2.26/0.99  inst_num_moves_active_passive:          12
% 2.26/0.99  inst_lit_activity:                      0
% 2.26/0.99  inst_lit_activity_moves:                0
% 2.26/0.99  inst_num_tautologies:                   0
% 2.26/0.99  inst_num_prop_implied:                  0
% 2.26/0.99  inst_num_existing_simplified:           0
% 2.26/0.99  inst_num_eq_res_simplified:             0
% 2.26/0.99  inst_num_child_elim:                    0
% 2.26/0.99  inst_num_of_dismatching_blockings:      67
% 2.26/0.99  inst_num_of_non_proper_insts:           224
% 2.26/0.99  inst_num_of_duplicates:                 0
% 2.26/0.99  inst_inst_num_from_inst_to_res:         0
% 2.26/0.99  inst_dismatching_checking_time:         0.
% 2.26/0.99  
% 2.26/0.99  ------ Resolution
% 2.26/0.99  
% 2.26/0.99  res_num_of_clauses:                     0
% 2.26/0.99  res_num_in_passive:                     0
% 2.26/0.99  res_num_in_active:                      0
% 2.26/0.99  res_num_of_loops:                       111
% 2.26/0.99  res_forward_subset_subsumed:            19
% 2.26/0.99  res_backward_subset_subsumed:           0
% 2.26/0.99  res_forward_subsumed:                   0
% 2.26/0.99  res_backward_subsumed:                  0
% 2.26/0.99  res_forward_subsumption_resolution:     0
% 2.26/0.99  res_backward_subsumption_resolution:    0
% 2.26/0.99  res_clause_to_clause_subsumption:       310
% 2.26/0.99  res_orphan_elimination:                 0
% 2.26/0.99  res_tautology_del:                      25
% 2.26/0.99  res_num_eq_res_simplified:              0
% 2.26/0.99  res_num_sel_changes:                    0
% 2.26/0.99  res_moves_from_active_to_pass:          0
% 2.26/0.99  
% 2.26/0.99  ------ Superposition
% 2.26/0.99  
% 2.26/0.99  sup_time_total:                         0.
% 2.26/0.99  sup_time_generating:                    0.
% 2.26/0.99  sup_time_sim_full:                      0.
% 2.26/0.99  sup_time_sim_immed:                     0.
% 2.26/0.99  
% 2.26/0.99  sup_num_of_clauses:                     66
% 2.26/0.99  sup_num_in_active:                      31
% 2.26/0.99  sup_num_in_passive:                     35
% 2.26/0.99  sup_num_of_loops:                       30
% 2.26/0.99  sup_fw_superposition:                   42
% 2.26/0.99  sup_bw_superposition:                   4
% 2.26/0.99  sup_immediate_simplified:               14
% 2.26/0.99  sup_given_eliminated:                   0
% 2.26/0.99  comparisons_done:                       0
% 2.26/0.99  comparisons_avoided:                    0
% 2.26/0.99  
% 2.26/0.99  ------ Simplifications
% 2.26/0.99  
% 2.26/0.99  
% 2.26/0.99  sim_fw_subset_subsumed:                 0
% 2.26/0.99  sim_bw_subset_subsumed:                 0
% 2.26/0.99  sim_fw_subsumed:                        0
% 2.26/0.99  sim_bw_subsumed:                        0
% 2.26/0.99  sim_fw_subsumption_res:                 0
% 2.26/0.99  sim_bw_subsumption_res:                 0
% 2.26/0.99  sim_tautology_del:                      0
% 2.26/0.99  sim_eq_tautology_del:                   0
% 2.26/0.99  sim_eq_res_simp:                        0
% 2.26/0.99  sim_fw_demodulated:                     0
% 2.26/0.99  sim_bw_demodulated:                     0
% 2.26/0.99  sim_light_normalised:                   14
% 2.26/0.99  sim_joinable_taut:                      0
% 2.26/0.99  sim_joinable_simp:                      0
% 2.26/0.99  sim_ac_normalised:                      0
% 2.26/0.99  sim_smt_subsumption:                    0
% 2.26/0.99  
%------------------------------------------------------------------------------
