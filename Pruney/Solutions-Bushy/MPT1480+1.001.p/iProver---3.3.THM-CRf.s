%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1480+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:43 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 484 expanded)
%              Number of clauses        :   85 ( 122 expanded)
%              Number of leaves         :    8 ( 137 expanded)
%              Depth                    :   20
%              Number of atoms          :  881 (3304 expanded)
%              Number of equality atoms :   80 ( 446 expanded)
%              Maximal formula depth    :   18 (   8 average)
%              Maximal clause size      :   21 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k10_lattice3(X0,X1,X2) != k10_lattice3(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k10_lattice3(X0,X1,X2) != k10_lattice3(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k10_lattice3(X0,X1,X2) != k10_lattice3(X0,X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k10_lattice3(X0,X1,sK3) != k10_lattice3(X0,sK3,X1)
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k10_lattice3(X0,X1,X2) != k10_lattice3(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k10_lattice3(X0,X2,sK2) != k10_lattice3(X0,sK2,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k10_lattice3(X0,X1,X2) != k10_lattice3(X0,X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k10_lattice3(sK1,X1,X2) != k10_lattice3(sK1,X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK1)) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_orders_2(sK1)
      & v1_lattice3(sK1)
      & v5_orders_2(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( k10_lattice3(sK1,sK2,sK3) != k10_lattice3(sK1,sK3,sK2)
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_orders_2(sK1)
    & v1_lattice3(sK1)
    & v5_orders_2(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f13,f21,f20,f19])).

fof(f34,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
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

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f17,plain,(
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

fof(f18,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f7,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f6])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f33,plain,(
    v1_lattice3(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f32,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f25,plain,(
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
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f27,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X3,X5)
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,(
    ! [X2,X0,X5,X1] :
      ( r1_orders_2(X0,k10_lattice3(X0,X1,X2),X5)
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X3,sK0(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X0,X1,X2) = X3
      | r1_orders_2(X0,X1,sK0(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X0,X1,X2) = X3
      | r1_orders_2(X0,X2,sK0(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X0,X1,X2) = X3
      | m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f37,plain,(
    k10_lattice3(sK1,sK2,sK3) != k10_lattice3(sK1,sK3,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f36,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f35,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k10_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_12,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_443,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k10_lattice3(X1,X2,X0),u1_struct_0(X1))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_12])).

cnf(c_444,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | m1_subset_1(k10_lattice3(sK1,X0,X1),u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_443])).

cnf(c_543,plain,
    ( ~ m1_subset_1(X0_41,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_41,u1_struct_0(sK1))
    | m1_subset_1(k10_lattice3(sK1,X0_41,X1_41),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_444])).

cnf(c_2178,plain,
    ( m1_subset_1(k10_lattice3(sK1,sK3,sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_543])).

cnf(c_7,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_84,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7,c_0])).

cnf(c_85,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0) ),
    inference(renaming,[status(thm)],[c_84])).

cnf(c_13,negated_conjecture,
    ( v1_lattice3(sK1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_349,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_85,c_13])).

cnf(c_350,plain,
    ( r1_orders_2(sK1,X0,k10_lattice3(sK1,X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k10_lattice3(sK1,X1,X0),u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_349])).

cnf(c_14,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_354,plain,
    ( r1_orders_2(sK1,X0,k10_lattice3(sK1,X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k10_lattice3(sK1,X1,X0),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_350,c_14,c_12])).

cnf(c_355,plain,
    ( r1_orders_2(sK1,X0,k10_lattice3(sK1,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k10_lattice3(sK1,X1,X0),u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_354])).

cnf(c_463,plain,
    ( r1_orders_2(sK1,X0,k10_lattice3(sK1,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_444,c_355])).

cnf(c_540,plain,
    ( r1_orders_2(sK1,X0_41,k10_lattice3(sK1,X1_41,X0_41))
    | ~ m1_subset_1(X1_41,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_41,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_463])).

cnf(c_1676,plain,
    ( r1_orders_2(sK1,sK2,k10_lattice3(sK1,sK3,sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_540])).

cnf(c_8,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_77,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_0])).

cnf(c_78,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0) ),
    inference(renaming,[status(thm)],[c_77])).

cnf(c_373,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_78,c_13])).

cnf(c_374,plain,
    ( r1_orders_2(sK1,X0,k10_lattice3(sK1,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k10_lattice3(sK1,X0,X1),u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_373])).

cnf(c_376,plain,
    ( r1_orders_2(sK1,X0,k10_lattice3(sK1,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k10_lattice3(sK1,X0,X1),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_374,c_14,c_12])).

cnf(c_377,plain,
    ( r1_orders_2(sK1,X0,k10_lattice3(sK1,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k10_lattice3(sK1,X0,X1),u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_376])).

cnf(c_462,plain,
    ( r1_orders_2(sK1,X0,k10_lattice3(sK1,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_444,c_377])).

cnf(c_541,plain,
    ( r1_orders_2(sK1,X0_41,k10_lattice3(sK1,X0_41,X1_41))
    | ~ m1_subset_1(X1_41,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_41,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_462])).

cnf(c_1115,plain,
    ( r1_orders_2(sK1,sK3,k10_lattice3(sK1,sK3,sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_541])).

cnf(c_6,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,k10_lattice3(X0,X3,X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X3,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_89,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(k10_lattice3(X0,X3,X1),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_orders_2(X0,k10_lattice3(X0,X3,X1),X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X1,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6,c_0])).

cnf(c_90,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,k10_lattice3(X0,X3,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X3,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0) ),
    inference(renaming,[status(thm)],[c_89])).

cnf(c_316,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,k10_lattice3(X0,X3,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X3,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_90,c_13])).

cnf(c_317,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X2,X1)
    | r1_orders_2(sK1,k10_lattice3(sK1,X0,X2),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k10_lattice3(sK1,X0,X2),u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_316])).

cnf(c_321,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X2,X1)
    | r1_orders_2(sK1,k10_lattice3(sK1,X0,X2),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k10_lattice3(sK1,X0,X2),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_317,c_14,c_12])).

cnf(c_322,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X2,X1)
    | r1_orders_2(sK1,k10_lattice3(sK1,X0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k10_lattice3(sK1,X0,X2),u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_321])).

cnf(c_461,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X2,X1)
    | r1_orders_2(sK1,k10_lattice3(sK1,X0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_444,c_322])).

cnf(c_542,plain,
    ( ~ r1_orders_2(sK1,X0_41,X1_41)
    | ~ r1_orders_2(sK1,X2_41,X1_41)
    | r1_orders_2(sK1,k10_lattice3(sK1,X0_41,X2_41),X1_41)
    | ~ m1_subset_1(X1_41,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_41,u1_struct_0(sK1))
    | ~ m1_subset_1(X2_41,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_461])).

cnf(c_1079,plain,
    ( ~ r1_orders_2(sK1,X0_41,sK0(sK1,sK2,sK3,k10_lattice3(sK1,sK3,sK2)))
    | r1_orders_2(sK1,k10_lattice3(sK1,sK3,X0_41),sK0(sK1,sK2,sK3,k10_lattice3(sK1,sK3,sK2)))
    | ~ r1_orders_2(sK1,sK3,sK0(sK1,sK2,sK3,k10_lattice3(sK1,sK3,sK2)))
    | ~ m1_subset_1(X0_41,u1_struct_0(sK1))
    | ~ m1_subset_1(sK0(sK1,sK2,sK3,k10_lattice3(sK1,sK3,sK2)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_542])).

cnf(c_1101,plain,
    ( r1_orders_2(sK1,k10_lattice3(sK1,sK3,sK2),sK0(sK1,sK2,sK3,k10_lattice3(sK1,sK3,sK2)))
    | ~ r1_orders_2(sK1,sK3,sK0(sK1,sK2,sK3,k10_lattice3(sK1,sK3,sK2)))
    | ~ r1_orders_2(sK1,sK2,sK0(sK1,sK2,sK3,k10_lattice3(sK1,sK3,sK2)))
    | ~ m1_subset_1(sK0(sK1,sK2,sK3,k10_lattice3(sK1,sK3,sK2)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1079])).

cnf(c_2,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X3,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_115,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X2,sK0(X0,X3,X1,X2))
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X1,X2)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2,c_0])).

cnf(c_116,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X3,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(renaming,[status(thm)],[c_115])).

cnf(c_188,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X3,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X3,X1) = X2
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_116,c_13])).

cnf(c_189,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X2,X1)
    | ~ r1_orders_2(sK1,X1,sK0(sK1,X0,X2,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | k10_lattice3(sK1,X0,X2) = X1 ),
    inference(unflattening,[status(thm)],[c_188])).

cnf(c_193,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X2,X1)
    | ~ r1_orders_2(sK1,X1,sK0(sK1,X0,X2,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k10_lattice3(sK1,X0,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_189,c_14,c_12])).

cnf(c_194,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X2,X1)
    | ~ r1_orders_2(sK1,X1,sK0(sK1,X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k10_lattice3(sK1,X0,X2) = X1 ),
    inference(renaming,[status(thm)],[c_193])).

cnf(c_547,plain,
    ( ~ r1_orders_2(sK1,X0_41,X1_41)
    | ~ r1_orders_2(sK1,X2_41,X1_41)
    | ~ r1_orders_2(sK1,X1_41,sK0(sK1,X0_41,X2_41,X1_41))
    | ~ m1_subset_1(X1_41,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_41,u1_struct_0(sK1))
    | ~ m1_subset_1(X2_41,u1_struct_0(sK1))
    | k10_lattice3(sK1,X0_41,X2_41) = X1_41 ),
    inference(subtyping,[status(esa)],[c_194])).

cnf(c_864,plain,
    ( ~ r1_orders_2(sK1,X0_41,k10_lattice3(sK1,X1_41,X0_41))
    | ~ r1_orders_2(sK1,X2_41,k10_lattice3(sK1,X1_41,X0_41))
    | ~ r1_orders_2(sK1,k10_lattice3(sK1,X1_41,X0_41),sK0(sK1,X0_41,X2_41,k10_lattice3(sK1,X1_41,X0_41)))
    | ~ m1_subset_1(X0_41,u1_struct_0(sK1))
    | ~ m1_subset_1(X2_41,u1_struct_0(sK1))
    | ~ m1_subset_1(k10_lattice3(sK1,X1_41,X0_41),u1_struct_0(sK1))
    | k10_lattice3(sK1,X0_41,X2_41) = k10_lattice3(sK1,X1_41,X0_41) ),
    inference(instantiation,[status(thm)],[c_547])).

cnf(c_1019,plain,
    ( ~ r1_orders_2(sK1,k10_lattice3(sK1,sK3,sK2),sK0(sK1,sK2,sK3,k10_lattice3(sK1,sK3,sK2)))
    | ~ r1_orders_2(sK1,sK3,k10_lattice3(sK1,sK3,sK2))
    | ~ r1_orders_2(sK1,sK2,k10_lattice3(sK1,sK3,sK2))
    | ~ m1_subset_1(k10_lattice3(sK1,sK3,sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k10_lattice3(sK1,sK2,sK3) = k10_lattice3(sK1,sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_864])).

cnf(c_4,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X3,sK0(X0,X3,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_103,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_orders_2(X0,X3,sK0(X0,X3,X1,X2))
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X1,X2)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4,c_0])).

cnf(c_104,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X3,sK0(X0,X3,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(renaming,[status(thm)],[c_103])).

cnf(c_254,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X3,sK0(X0,X3,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X3,X1) = X2
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_104,c_13])).

cnf(c_255,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X2,X1)
    | r1_orders_2(sK1,X0,sK0(sK1,X0,X2,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | k10_lattice3(sK1,X0,X2) = X1 ),
    inference(unflattening,[status(thm)],[c_254])).

cnf(c_257,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X2,X1)
    | r1_orders_2(sK1,X0,sK0(sK1,X0,X2,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k10_lattice3(sK1,X0,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_255,c_14,c_12])).

cnf(c_258,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X2,X1)
    | r1_orders_2(sK1,X0,sK0(sK1,X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k10_lattice3(sK1,X0,X2) = X1 ),
    inference(renaming,[status(thm)],[c_257])).

cnf(c_545,plain,
    ( ~ r1_orders_2(sK1,X0_41,X1_41)
    | ~ r1_orders_2(sK1,X2_41,X1_41)
    | r1_orders_2(sK1,X0_41,sK0(sK1,X0_41,X2_41,X1_41))
    | ~ m1_subset_1(X1_41,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_41,u1_struct_0(sK1))
    | ~ m1_subset_1(X2_41,u1_struct_0(sK1))
    | k10_lattice3(sK1,X0_41,X2_41) = X1_41 ),
    inference(subtyping,[status(esa)],[c_258])).

cnf(c_866,plain,
    ( r1_orders_2(sK1,X0_41,sK0(sK1,X0_41,X1_41,k10_lattice3(sK1,X2_41,X0_41)))
    | ~ r1_orders_2(sK1,X0_41,k10_lattice3(sK1,X2_41,X0_41))
    | ~ r1_orders_2(sK1,X1_41,k10_lattice3(sK1,X2_41,X0_41))
    | ~ m1_subset_1(X0_41,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_41,u1_struct_0(sK1))
    | ~ m1_subset_1(k10_lattice3(sK1,X2_41,X0_41),u1_struct_0(sK1))
    | k10_lattice3(sK1,X0_41,X1_41) = k10_lattice3(sK1,X2_41,X0_41) ),
    inference(instantiation,[status(thm)],[c_545])).

cnf(c_984,plain,
    ( ~ r1_orders_2(sK1,sK3,k10_lattice3(sK1,sK3,sK2))
    | r1_orders_2(sK1,sK2,sK0(sK1,sK2,sK3,k10_lattice3(sK1,sK3,sK2)))
    | ~ r1_orders_2(sK1,sK2,k10_lattice3(sK1,sK3,sK2))
    | ~ m1_subset_1(k10_lattice3(sK1,sK3,sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k10_lattice3(sK1,sK2,sK3) = k10_lattice3(sK1,sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_866])).

cnf(c_3,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X1,sK0(X0,X3,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_110,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_orders_2(X0,X1,sK0(X0,X3,X1,X2))
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X1,X2)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3,c_0])).

cnf(c_111,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X1,sK0(X0,X3,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(renaming,[status(thm)],[c_110])).

cnf(c_221,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X1,sK0(X0,X3,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X3,X1) = X2
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_111,c_13])).

cnf(c_222,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X2,X1)
    | r1_orders_2(sK1,X2,sK0(sK1,X0,X2,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | k10_lattice3(sK1,X0,X2) = X1 ),
    inference(unflattening,[status(thm)],[c_221])).

cnf(c_226,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X2,X1)
    | r1_orders_2(sK1,X2,sK0(sK1,X0,X2,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k10_lattice3(sK1,X0,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_222,c_14,c_12])).

cnf(c_227,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X2,X1)
    | r1_orders_2(sK1,X2,sK0(sK1,X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k10_lattice3(sK1,X0,X2) = X1 ),
    inference(renaming,[status(thm)],[c_226])).

cnf(c_546,plain,
    ( ~ r1_orders_2(sK1,X0_41,X1_41)
    | ~ r1_orders_2(sK1,X2_41,X1_41)
    | r1_orders_2(sK1,X2_41,sK0(sK1,X0_41,X2_41,X1_41))
    | ~ m1_subset_1(X1_41,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_41,u1_struct_0(sK1))
    | ~ m1_subset_1(X2_41,u1_struct_0(sK1))
    | k10_lattice3(sK1,X0_41,X2_41) = X1_41 ),
    inference(subtyping,[status(esa)],[c_227])).

cnf(c_865,plain,
    ( r1_orders_2(sK1,X0_41,sK0(sK1,X1_41,X0_41,k10_lattice3(sK1,X2_41,X1_41)))
    | ~ r1_orders_2(sK1,X1_41,k10_lattice3(sK1,X2_41,X1_41))
    | ~ r1_orders_2(sK1,X0_41,k10_lattice3(sK1,X2_41,X1_41))
    | ~ m1_subset_1(X1_41,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_41,u1_struct_0(sK1))
    | ~ m1_subset_1(k10_lattice3(sK1,X2_41,X1_41),u1_struct_0(sK1))
    | k10_lattice3(sK1,X1_41,X0_41) = k10_lattice3(sK1,X2_41,X1_41) ),
    inference(instantiation,[status(thm)],[c_546])).

cnf(c_953,plain,
    ( r1_orders_2(sK1,sK3,sK0(sK1,sK2,sK3,k10_lattice3(sK1,sK3,sK2)))
    | ~ r1_orders_2(sK1,sK3,k10_lattice3(sK1,sK3,sK2))
    | ~ r1_orders_2(sK1,sK2,k10_lattice3(sK1,sK3,sK2))
    | ~ m1_subset_1(k10_lattice3(sK1,sK3,sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k10_lattice3(sK1,sK2,sK3) = k10_lattice3(sK1,sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_865])).

cnf(c_5,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X3,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_96,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | m1_subset_1(sK0(X0,X3,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X1,X2)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5,c_0])).

cnf(c_97,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X3,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(renaming,[status(thm)],[c_96])).

cnf(c_283,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X3,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X3,X1) = X2
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_97,c_13])).

cnf(c_284,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | m1_subset_1(sK0(sK1,X0,X2,X1),u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | k10_lattice3(sK1,X0,X2) = X1 ),
    inference(unflattening,[status(thm)],[c_283])).

cnf(c_288,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | m1_subset_1(sK0(sK1,X0,X2,X1),u1_struct_0(sK1))
    | k10_lattice3(sK1,X0,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_284,c_14,c_12])).

cnf(c_289,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK1,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(sK0(sK1,X0,X2,X1),u1_struct_0(sK1))
    | k10_lattice3(sK1,X0,X2) = X1 ),
    inference(renaming,[status(thm)],[c_288])).

cnf(c_544,plain,
    ( ~ r1_orders_2(sK1,X0_41,X1_41)
    | ~ r1_orders_2(sK1,X2_41,X1_41)
    | ~ m1_subset_1(X1_41,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_41,u1_struct_0(sK1))
    | ~ m1_subset_1(X2_41,u1_struct_0(sK1))
    | m1_subset_1(sK0(sK1,X0_41,X2_41,X1_41),u1_struct_0(sK1))
    | k10_lattice3(sK1,X0_41,X2_41) = X1_41 ),
    inference(subtyping,[status(esa)],[c_289])).

cnf(c_867,plain,
    ( ~ r1_orders_2(sK1,X0_41,k10_lattice3(sK1,X1_41,X0_41))
    | ~ r1_orders_2(sK1,X2_41,k10_lattice3(sK1,X1_41,X0_41))
    | ~ m1_subset_1(X0_41,u1_struct_0(sK1))
    | ~ m1_subset_1(X2_41,u1_struct_0(sK1))
    | m1_subset_1(sK0(sK1,X0_41,X2_41,k10_lattice3(sK1,X1_41,X0_41)),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_lattice3(sK1,X1_41,X0_41),u1_struct_0(sK1))
    | k10_lattice3(sK1,X0_41,X2_41) = k10_lattice3(sK1,X1_41,X0_41) ),
    inference(instantiation,[status(thm)],[c_544])).

cnf(c_946,plain,
    ( ~ r1_orders_2(sK1,sK3,k10_lattice3(sK1,sK3,sK2))
    | ~ r1_orders_2(sK1,sK2,k10_lattice3(sK1,sK3,sK2))
    | m1_subset_1(sK0(sK1,sK2,sK3,k10_lattice3(sK1,sK3,sK2)),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_lattice3(sK1,sK3,sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k10_lattice3(sK1,sK2,sK3) = k10_lattice3(sK1,sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_867])).

cnf(c_9,negated_conjecture,
    ( k10_lattice3(sK1,sK2,sK3) != k10_lattice3(sK1,sK3,sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_550,negated_conjecture,
    ( k10_lattice3(sK1,sK2,sK3) != k10_lattice3(sK1,sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2178,c_1676,c_1115,c_1101,c_1019,c_984,c_953,c_946,c_550,c_10,c_11])).


%------------------------------------------------------------------------------
