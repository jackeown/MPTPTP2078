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
% DateTime   : Thu Dec  3 12:19:04 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 687 expanded)
%              Number of clauses        :   93 ( 180 expanded)
%              Number of leaves         :   15 ( 202 expanded)
%              Depth                    :   19
%              Number of atoms          :  941 (4420 expanded)
%              Number of equality atoms :  114 ( 613 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   21 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f41,plain,(
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

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f40,f41])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f30,plain,(
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
    inference(flattening,[],[f30])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,sK4)) != X1
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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

fof(f43,plain,
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

fof(f46,plain,
    ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_orders_2(sK2)
    & v2_lattice3(sK2)
    & v1_lattice3(sK2)
    & v5_orders_2(sK2)
    & v3_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f31,f45,f44,f43])).

fof(f72,plain,(
    v2_lattice3(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f70,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f73,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f64,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f75,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f46])).

fof(f74,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f46])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f71,plain,(
    v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f76,plain,(
    k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f36,plain,(
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

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).

fof(f53,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f69,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_13,plain,
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
    inference(cnf_transformation,[],[f66])).

cnf(c_4,plain,
    ( ~ v2_lattice3(X0)
    | ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_201,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_4])).

cnf(c_202,plain,
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
    inference(renaming,[status(thm)],[c_201])).

cnf(c_26,negated_conjecture,
    ( v2_lattice3(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_770,plain,
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
    inference(resolution_lifted,[status(thm)],[c_202,c_26])).

cnf(c_771,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | ~ r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k11_lattice3(sK2,X2,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_770])).

cnf(c_28,negated_conjecture,
    ( v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_25,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_775,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | ~ r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | k11_lattice3(sK2,X2,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_771,c_28,c_25])).

cnf(c_776,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | ~ r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k11_lattice3(sK2,X2,X1) = X0 ),
    inference(renaming,[status(thm)],[c_775])).

cnf(c_1222,plain,
    ( ~ r1_orders_2(sK2,X0_48,X1_48)
    | ~ r1_orders_2(sK2,X0_48,X2_48)
    | ~ r1_orders_2(sK2,sK1(sK2,X2_48,X1_48,X0_48),X0_48)
    | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
    | ~ m1_subset_1(X2_48,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | k11_lattice3(sK2,X2_48,X1_48) = X0_48 ),
    inference(subtyping,[status(esa)],[c_776])).

cnf(c_6775,plain,
    ( ~ r1_orders_2(sK2,sK1(sK2,X0_48,k10_lattice3(sK2,sK3,sK4),sK3),sK3)
    | ~ r1_orders_2(sK2,sK3,X0_48)
    | ~ r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK4))
    | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k11_lattice3(sK2,X0_48,k10_lattice3(sK2,sK3,sK4)) = sK3 ),
    inference(instantiation,[status(thm)],[c_1222])).

cnf(c_6792,plain,
    ( ~ r1_orders_2(sK2,sK1(sK2,sK3,k10_lattice3(sK2,sK3,sK4),sK3),sK3)
    | ~ r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK4))
    | ~ r1_orders_2(sK2,sK3,sK3)
    | ~ m1_subset_1(k10_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k11_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,sK4)) = sK3 ),
    inference(instantiation,[status(thm)],[c_6775])).

cnf(c_15,plain,
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
    inference(cnf_transformation,[],[f64])).

cnf(c_189,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_4])).

cnf(c_190,plain,
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
    inference(renaming,[status(thm)],[c_189])).

cnf(c_836,plain,
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
    inference(resolution_lifted,[status(thm)],[c_190,c_26])).

cnf(c_837,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k11_lattice3(sK2,X2,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_836])).

cnf(c_839,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | k11_lattice3(sK2,X2,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_837,c_28,c_25])).

cnf(c_840,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k11_lattice3(sK2,X2,X1) = X0 ),
    inference(renaming,[status(thm)],[c_839])).

cnf(c_1220,plain,
    ( ~ r1_orders_2(sK2,X0_48,X1_48)
    | ~ r1_orders_2(sK2,X0_48,X2_48)
    | r1_orders_2(sK2,sK1(sK2,X2_48,X1_48,X0_48),X2_48)
    | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
    | ~ m1_subset_1(X2_48,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | k11_lattice3(sK2,X2_48,X1_48) = X0_48 ),
    inference(subtyping,[status(esa)],[c_840])).

cnf(c_6777,plain,
    ( r1_orders_2(sK2,sK1(sK2,X0_48,k10_lattice3(sK2,sK3,sK4),sK3),X0_48)
    | ~ r1_orders_2(sK2,sK3,X0_48)
    | ~ r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK4))
    | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k11_lattice3(sK2,X0_48,k10_lattice3(sK2,sK3,sK4)) = sK3 ),
    inference(instantiation,[status(thm)],[c_1220])).

cnf(c_6784,plain,
    ( r1_orders_2(sK2,sK1(sK2,sK3,k10_lattice3(sK2,sK3,sK4),sK3),sK3)
    | ~ r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK4))
    | ~ r1_orders_2(sK2,sK3,sK3)
    | ~ m1_subset_1(k10_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k11_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,sK4)) = sK3 ),
    inference(instantiation,[status(thm)],[c_6777])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1230,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1612,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1230])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1229,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1613,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1229])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k10_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1050,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k10_lattice3(X1,X2,X0),u1_struct_0(X1))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_25])).

cnf(c_1051,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_1050])).

cnf(c_1214,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
    | m1_subset_1(k10_lattice3(sK2,X0_48,X1_48),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_1051])).

cnf(c_1630,plain,
    ( m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_48,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k10_lattice3(sK2,X0_48,X1_48),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1214])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_975,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_26])).

cnf(c_976,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k12_lattice3(sK2,X0,X1) = k11_lattice3(sK2,X0,X1) ),
    inference(unflattening,[status(thm)],[c_975])).

cnf(c_980,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k12_lattice3(sK2,X0,X1) = k11_lattice3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_976,c_28,c_25])).

cnf(c_981,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k12_lattice3(sK2,X1,X0) = k11_lattice3(sK2,X1,X0) ),
    inference(renaming,[status(thm)],[c_980])).

cnf(c_1215,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
    | k12_lattice3(sK2,X1_48,X0_48) = k11_lattice3(sK2,X1_48,X0_48) ),
    inference(subtyping,[status(esa)],[c_981])).

cnf(c_1629,plain,
    ( k12_lattice3(sK2,X0_48,X1_48) = k11_lattice3(sK2,X0_48,X1_48)
    | m1_subset_1(X1_48,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1215])).

cnf(c_2251,plain,
    ( k12_lattice3(sK2,sK3,X0_48) = k11_lattice3(sK2,sK3,X0_48)
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1613,c_1629])).

cnf(c_2765,plain,
    ( k12_lattice3(sK2,sK3,k10_lattice3(sK2,X0_48,X1_48)) = k11_lattice3(sK2,sK3,k10_lattice3(sK2,X0_48,X1_48))
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_48,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1630,c_2251])).

cnf(c_2844,plain,
    ( k12_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,X0_48)) = k11_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,X0_48))
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1613,c_2765])).

cnf(c_3199,plain,
    ( k12_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,sK4)) = k11_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_1612,c_2844])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k13_lattice3(X1,X2,X0) = k10_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_27,negated_conjecture,
    ( v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_695,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k13_lattice3(X1,X2,X0) = k10_lattice3(X1,X2,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_696,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k13_lattice3(sK2,X0,X1) = k10_lattice3(sK2,X0,X1) ),
    inference(unflattening,[status(thm)],[c_695])).

cnf(c_700,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k13_lattice3(sK2,X0,X1) = k10_lattice3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_696,c_28,c_25])).

cnf(c_701,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k13_lattice3(sK2,X1,X0) = k10_lattice3(sK2,X1,X0) ),
    inference(renaming,[status(thm)],[c_700])).

cnf(c_1223,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
    | k13_lattice3(sK2,X1_48,X0_48) = k10_lattice3(sK2,X1_48,X0_48) ),
    inference(subtyping,[status(esa)],[c_701])).

cnf(c_1621,plain,
    ( k13_lattice3(sK2,X0_48,X1_48) = k10_lattice3(sK2,X0_48,X1_48)
    | m1_subset_1(X1_48,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1223])).

cnf(c_1892,plain,
    ( k13_lattice3(sK2,sK3,X0_48) = k10_lattice3(sK2,sK3,X0_48)
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1613,c_1621])).

cnf(c_2000,plain,
    ( k13_lattice3(sK2,sK3,sK4) = k10_lattice3(sK2,sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1612,c_1892])).

cnf(c_22,negated_conjecture,
    ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1231,negated_conjecture,
    ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_2153,plain,
    ( k12_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,sK4)) != sK3 ),
    inference(demodulation,[status(thm)],[c_2000,c_1231])).

cnf(c_3286,plain,
    ( k11_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,sK4)) != sK3 ),
    inference(demodulation,[status(thm)],[c_3199,c_2153])).

cnf(c_12,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_3,plain,
    ( ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_208,plain,
    ( ~ v1_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_3])).

cnf(c_209,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_208])).

cnf(c_675,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_209,c_27])).

cnf(c_676,plain,
    ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_675])).

cnf(c_678,plain,
    ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_676,c_28,c_25])).

cnf(c_679,plain,
    ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_678])).

cnf(c_1068,plain,
    ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1051,c_679])).

cnf(c_1213,plain,
    ( r1_orders_2(sK2,X0_48,k10_lattice3(sK2,X0_48,X1_48))
    | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_48,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_1068])).

cnf(c_2448,plain,
    ( r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK4))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1213])).

cnf(c_2235,plain,
    ( m1_subset_1(k10_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1214])).

cnf(c_2,plain,
    ( r3_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_29,negated_conjecture,
    ( v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_387,plain,
    ( r3_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_29])).

cnf(c_388,plain,
    ( r3_orders_2(sK2,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_387])).

cnf(c_81,plain,
    ( ~ v2_lattice3(sK2)
    | ~ v2_struct_0(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_392,plain,
    ( r3_orders_2(sK2,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_388,c_26,c_25,c_81])).

cnf(c_393,plain,
    ( r3_orders_2(sK2,X0,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_392])).

cnf(c_1,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_408,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_29])).

cnf(c_409,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ r3_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_408])).

cnf(c_413,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ r3_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_409,c_26,c_25,c_81])).

cnf(c_414,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ r3_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_413])).

cnf(c_471,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X3,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | X0 != X3
    | X1 != X3
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_393,c_414])).

cnf(c_472,plain,
    ( r1_orders_2(sK2,X0,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_471])).

cnf(c_1228,plain,
    ( r1_orders_2(sK2,X0_48,X0_48)
    | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_48,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_472])).

cnf(c_1232,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1228])).

cnf(c_1255,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ sP0_iProver_split ),
    inference(instantiation,[status(thm)],[c_1232])).

cnf(c_1233,plain,
    ( r1_orders_2(sK2,X0_48,X0_48)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_1228])).

cnf(c_1252,plain,
    ( r1_orders_2(sK2,sK3,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ sP1_iProver_split ),
    inference(instantiation,[status(thm)],[c_1233])).

cnf(c_1234,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1228])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6792,c_6784,c_3286,c_2448,c_2235,c_1255,c_1252,c_1234,c_23,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:21:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.97/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.00  
% 2.97/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.97/1.00  
% 2.97/1.00  ------  iProver source info
% 2.97/1.00  
% 2.97/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.97/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.97/1.00  git: non_committed_changes: false
% 2.97/1.00  git: last_make_outside_of_git: false
% 2.97/1.00  
% 2.97/1.00  ------ 
% 2.97/1.00  
% 2.97/1.00  ------ Input Options
% 2.97/1.00  
% 2.97/1.00  --out_options                           all
% 2.97/1.00  --tptp_safe_out                         true
% 2.97/1.00  --problem_path                          ""
% 2.97/1.00  --include_path                          ""
% 2.97/1.00  --clausifier                            res/vclausify_rel
% 2.97/1.00  --clausifier_options                    --mode clausify
% 2.97/1.00  --stdin                                 false
% 2.97/1.00  --stats_out                             all
% 2.97/1.00  
% 2.97/1.00  ------ General Options
% 2.97/1.00  
% 2.97/1.00  --fof                                   false
% 2.97/1.00  --time_out_real                         305.
% 2.97/1.00  --time_out_virtual                      -1.
% 2.97/1.00  --symbol_type_check                     false
% 2.97/1.00  --clausify_out                          false
% 2.97/1.00  --sig_cnt_out                           false
% 2.97/1.00  --trig_cnt_out                          false
% 2.97/1.00  --trig_cnt_out_tolerance                1.
% 2.97/1.00  --trig_cnt_out_sk_spl                   false
% 2.97/1.00  --abstr_cl_out                          false
% 2.97/1.00  
% 2.97/1.00  ------ Global Options
% 2.97/1.00  
% 2.97/1.00  --schedule                              default
% 2.97/1.00  --add_important_lit                     false
% 2.97/1.00  --prop_solver_per_cl                    1000
% 2.97/1.00  --min_unsat_core                        false
% 2.97/1.00  --soft_assumptions                      false
% 2.97/1.00  --soft_lemma_size                       3
% 2.97/1.00  --prop_impl_unit_size                   0
% 2.97/1.00  --prop_impl_unit                        []
% 2.97/1.00  --share_sel_clauses                     true
% 2.97/1.00  --reset_solvers                         false
% 2.97/1.00  --bc_imp_inh                            [conj_cone]
% 2.97/1.00  --conj_cone_tolerance                   3.
% 2.97/1.00  --extra_neg_conj                        none
% 2.97/1.00  --large_theory_mode                     true
% 2.97/1.00  --prolific_symb_bound                   200
% 2.97/1.00  --lt_threshold                          2000
% 2.97/1.00  --clause_weak_htbl                      true
% 2.97/1.00  --gc_record_bc_elim                     false
% 2.97/1.00  
% 2.97/1.00  ------ Preprocessing Options
% 2.97/1.00  
% 2.97/1.00  --preprocessing_flag                    true
% 2.97/1.00  --time_out_prep_mult                    0.1
% 2.97/1.00  --splitting_mode                        input
% 2.97/1.00  --splitting_grd                         true
% 2.97/1.00  --splitting_cvd                         false
% 2.97/1.00  --splitting_cvd_svl                     false
% 2.97/1.00  --splitting_nvd                         32
% 2.97/1.00  --sub_typing                            true
% 2.97/1.00  --prep_gs_sim                           true
% 2.97/1.00  --prep_unflatten                        true
% 2.97/1.00  --prep_res_sim                          true
% 2.97/1.00  --prep_upred                            true
% 2.97/1.00  --prep_sem_filter                       exhaustive
% 2.97/1.00  --prep_sem_filter_out                   false
% 2.97/1.00  --pred_elim                             true
% 2.97/1.00  --res_sim_input                         true
% 2.97/1.00  --eq_ax_congr_red                       true
% 2.97/1.00  --pure_diseq_elim                       true
% 2.97/1.00  --brand_transform                       false
% 2.97/1.00  --non_eq_to_eq                          false
% 2.97/1.00  --prep_def_merge                        true
% 2.97/1.00  --prep_def_merge_prop_impl              false
% 2.97/1.00  --prep_def_merge_mbd                    true
% 2.97/1.00  --prep_def_merge_tr_red                 false
% 2.97/1.00  --prep_def_merge_tr_cl                  false
% 2.97/1.00  --smt_preprocessing                     true
% 2.97/1.00  --smt_ac_axioms                         fast
% 2.97/1.00  --preprocessed_out                      false
% 2.97/1.00  --preprocessed_stats                    false
% 2.97/1.00  
% 2.97/1.00  ------ Abstraction refinement Options
% 2.97/1.00  
% 2.97/1.00  --abstr_ref                             []
% 2.97/1.00  --abstr_ref_prep                        false
% 2.97/1.00  --abstr_ref_until_sat                   false
% 2.97/1.00  --abstr_ref_sig_restrict                funpre
% 2.97/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.97/1.00  --abstr_ref_under                       []
% 2.97/1.00  
% 2.97/1.00  ------ SAT Options
% 2.97/1.00  
% 2.97/1.00  --sat_mode                              false
% 2.97/1.00  --sat_fm_restart_options                ""
% 2.97/1.00  --sat_gr_def                            false
% 2.97/1.00  --sat_epr_types                         true
% 2.97/1.00  --sat_non_cyclic_types                  false
% 2.97/1.00  --sat_finite_models                     false
% 2.97/1.00  --sat_fm_lemmas                         false
% 2.97/1.00  --sat_fm_prep                           false
% 2.97/1.00  --sat_fm_uc_incr                        true
% 2.97/1.00  --sat_out_model                         small
% 2.97/1.00  --sat_out_clauses                       false
% 2.97/1.00  
% 2.97/1.00  ------ QBF Options
% 2.97/1.00  
% 2.97/1.00  --qbf_mode                              false
% 2.97/1.00  --qbf_elim_univ                         false
% 2.97/1.00  --qbf_dom_inst                          none
% 2.97/1.00  --qbf_dom_pre_inst                      false
% 2.97/1.00  --qbf_sk_in                             false
% 2.97/1.00  --qbf_pred_elim                         true
% 2.97/1.00  --qbf_split                             512
% 2.97/1.00  
% 2.97/1.00  ------ BMC1 Options
% 2.97/1.00  
% 2.97/1.00  --bmc1_incremental                      false
% 2.97/1.00  --bmc1_axioms                           reachable_all
% 2.97/1.00  --bmc1_min_bound                        0
% 2.97/1.00  --bmc1_max_bound                        -1
% 2.97/1.00  --bmc1_max_bound_default                -1
% 2.97/1.00  --bmc1_symbol_reachability              true
% 2.97/1.00  --bmc1_property_lemmas                  false
% 2.97/1.00  --bmc1_k_induction                      false
% 2.97/1.00  --bmc1_non_equiv_states                 false
% 2.97/1.00  --bmc1_deadlock                         false
% 2.97/1.00  --bmc1_ucm                              false
% 2.97/1.00  --bmc1_add_unsat_core                   none
% 2.97/1.00  --bmc1_unsat_core_children              false
% 2.97/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.97/1.00  --bmc1_out_stat                         full
% 2.97/1.00  --bmc1_ground_init                      false
% 2.97/1.00  --bmc1_pre_inst_next_state              false
% 2.97/1.00  --bmc1_pre_inst_state                   false
% 2.97/1.00  --bmc1_pre_inst_reach_state             false
% 2.97/1.00  --bmc1_out_unsat_core                   false
% 2.97/1.00  --bmc1_aig_witness_out                  false
% 2.97/1.00  --bmc1_verbose                          false
% 2.97/1.00  --bmc1_dump_clauses_tptp                false
% 2.97/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.97/1.00  --bmc1_dump_file                        -
% 2.97/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.97/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.97/1.00  --bmc1_ucm_extend_mode                  1
% 2.97/1.00  --bmc1_ucm_init_mode                    2
% 2.97/1.00  --bmc1_ucm_cone_mode                    none
% 2.97/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.97/1.00  --bmc1_ucm_relax_model                  4
% 2.97/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.97/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.97/1.00  --bmc1_ucm_layered_model                none
% 2.97/1.00  --bmc1_ucm_max_lemma_size               10
% 2.97/1.00  
% 2.97/1.00  ------ AIG Options
% 2.97/1.00  
% 2.97/1.00  --aig_mode                              false
% 2.97/1.00  
% 2.97/1.00  ------ Instantiation Options
% 2.97/1.00  
% 2.97/1.00  --instantiation_flag                    true
% 2.97/1.00  --inst_sos_flag                         false
% 2.97/1.00  --inst_sos_phase                        true
% 2.97/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.97/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.97/1.00  --inst_lit_sel_side                     num_symb
% 2.97/1.00  --inst_solver_per_active                1400
% 2.97/1.00  --inst_solver_calls_frac                1.
% 2.97/1.00  --inst_passive_queue_type               priority_queues
% 2.97/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.97/1.00  --inst_passive_queues_freq              [25;2]
% 2.97/1.00  --inst_dismatching                      true
% 2.97/1.00  --inst_eager_unprocessed_to_passive     true
% 2.97/1.00  --inst_prop_sim_given                   true
% 2.97/1.00  --inst_prop_sim_new                     false
% 2.97/1.00  --inst_subs_new                         false
% 2.97/1.00  --inst_eq_res_simp                      false
% 2.97/1.00  --inst_subs_given                       false
% 2.97/1.00  --inst_orphan_elimination               true
% 2.97/1.00  --inst_learning_loop_flag               true
% 2.97/1.00  --inst_learning_start                   3000
% 2.97/1.00  --inst_learning_factor                  2
% 2.97/1.00  --inst_start_prop_sim_after_learn       3
% 2.97/1.00  --inst_sel_renew                        solver
% 2.97/1.00  --inst_lit_activity_flag                true
% 2.97/1.00  --inst_restr_to_given                   false
% 2.97/1.00  --inst_activity_threshold               500
% 2.97/1.00  --inst_out_proof                        true
% 2.97/1.00  
% 2.97/1.00  ------ Resolution Options
% 2.97/1.00  
% 2.97/1.00  --resolution_flag                       true
% 2.97/1.00  --res_lit_sel                           adaptive
% 2.97/1.00  --res_lit_sel_side                      none
% 2.97/1.00  --res_ordering                          kbo
% 2.97/1.00  --res_to_prop_solver                    active
% 2.97/1.00  --res_prop_simpl_new                    false
% 2.97/1.00  --res_prop_simpl_given                  true
% 2.97/1.00  --res_passive_queue_type                priority_queues
% 2.97/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.97/1.00  --res_passive_queues_freq               [15;5]
% 2.97/1.00  --res_forward_subs                      full
% 2.97/1.00  --res_backward_subs                     full
% 2.97/1.00  --res_forward_subs_resolution           true
% 2.97/1.00  --res_backward_subs_resolution          true
% 2.97/1.00  --res_orphan_elimination                true
% 2.97/1.00  --res_time_limit                        2.
% 2.97/1.00  --res_out_proof                         true
% 2.97/1.00  
% 2.97/1.00  ------ Superposition Options
% 2.97/1.00  
% 2.97/1.00  --superposition_flag                    true
% 2.97/1.00  --sup_passive_queue_type                priority_queues
% 2.97/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.97/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.97/1.00  --demod_completeness_check              fast
% 2.97/1.00  --demod_use_ground                      true
% 2.97/1.00  --sup_to_prop_solver                    passive
% 2.97/1.00  --sup_prop_simpl_new                    true
% 2.97/1.00  --sup_prop_simpl_given                  true
% 2.97/1.00  --sup_fun_splitting                     false
% 2.97/1.00  --sup_smt_interval                      50000
% 2.97/1.00  
% 2.97/1.00  ------ Superposition Simplification Setup
% 2.97/1.00  
% 2.97/1.00  --sup_indices_passive                   []
% 2.97/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.97/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.00  --sup_full_bw                           [BwDemod]
% 2.97/1.00  --sup_immed_triv                        [TrivRules]
% 2.97/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.97/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.00  --sup_immed_bw_main                     []
% 2.97/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.97/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/1.00  
% 2.97/1.00  ------ Combination Options
% 2.97/1.00  
% 2.97/1.00  --comb_res_mult                         3
% 2.97/1.00  --comb_sup_mult                         2
% 2.97/1.00  --comb_inst_mult                        10
% 2.97/1.00  
% 2.97/1.00  ------ Debug Options
% 2.97/1.00  
% 2.97/1.00  --dbg_backtrace                         false
% 2.97/1.00  --dbg_dump_prop_clauses                 false
% 2.97/1.00  --dbg_dump_prop_clauses_file            -
% 2.97/1.00  --dbg_out_stat                          false
% 2.97/1.00  ------ Parsing...
% 2.97/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.97/1.00  
% 2.97/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.97/1.00  
% 2.97/1.00  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.97/1.00  
% 2.97/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.97/1.00  ------ Proving...
% 2.97/1.00  ------ Problem Properties 
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  clauses                                 23
% 2.97/1.00  conjectures                             3
% 2.97/1.00  EPR                                     1
% 2.97/1.00  Horn                                    16
% 2.97/1.00  unary                                   3
% 2.97/1.00  binary                                  2
% 2.97/1.00  lits                                    102
% 2.97/1.00  lits eq                                 11
% 2.97/1.00  fd_pure                                 0
% 2.97/1.00  fd_pseudo                               0
% 2.97/1.00  fd_cond                                 0
% 2.97/1.00  fd_pseudo_cond                          8
% 2.97/1.00  AC symbols                              0
% 2.97/1.00  
% 2.97/1.00  ------ Schedule dynamic 5 is on 
% 2.97/1.00  
% 2.97/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  ------ 
% 2.97/1.00  Current options:
% 2.97/1.00  ------ 
% 2.97/1.00  
% 2.97/1.00  ------ Input Options
% 2.97/1.00  
% 2.97/1.00  --out_options                           all
% 2.97/1.00  --tptp_safe_out                         true
% 2.97/1.00  --problem_path                          ""
% 2.97/1.00  --include_path                          ""
% 2.97/1.00  --clausifier                            res/vclausify_rel
% 2.97/1.00  --clausifier_options                    --mode clausify
% 2.97/1.00  --stdin                                 false
% 2.97/1.00  --stats_out                             all
% 2.97/1.00  
% 2.97/1.00  ------ General Options
% 2.97/1.00  
% 2.97/1.00  --fof                                   false
% 2.97/1.00  --time_out_real                         305.
% 2.97/1.00  --time_out_virtual                      -1.
% 2.97/1.00  --symbol_type_check                     false
% 2.97/1.00  --clausify_out                          false
% 2.97/1.00  --sig_cnt_out                           false
% 2.97/1.00  --trig_cnt_out                          false
% 2.97/1.00  --trig_cnt_out_tolerance                1.
% 2.97/1.00  --trig_cnt_out_sk_spl                   false
% 2.97/1.00  --abstr_cl_out                          false
% 2.97/1.00  
% 2.97/1.00  ------ Global Options
% 2.97/1.00  
% 2.97/1.00  --schedule                              default
% 2.97/1.00  --add_important_lit                     false
% 2.97/1.00  --prop_solver_per_cl                    1000
% 2.97/1.00  --min_unsat_core                        false
% 2.97/1.00  --soft_assumptions                      false
% 2.97/1.00  --soft_lemma_size                       3
% 2.97/1.00  --prop_impl_unit_size                   0
% 2.97/1.00  --prop_impl_unit                        []
% 2.97/1.00  --share_sel_clauses                     true
% 2.97/1.00  --reset_solvers                         false
% 2.97/1.00  --bc_imp_inh                            [conj_cone]
% 2.97/1.00  --conj_cone_tolerance                   3.
% 2.97/1.00  --extra_neg_conj                        none
% 2.97/1.00  --large_theory_mode                     true
% 2.97/1.00  --prolific_symb_bound                   200
% 2.97/1.00  --lt_threshold                          2000
% 2.97/1.00  --clause_weak_htbl                      true
% 2.97/1.00  --gc_record_bc_elim                     false
% 2.97/1.00  
% 2.97/1.00  ------ Preprocessing Options
% 2.97/1.00  
% 2.97/1.00  --preprocessing_flag                    true
% 2.97/1.00  --time_out_prep_mult                    0.1
% 2.97/1.00  --splitting_mode                        input
% 2.97/1.00  --splitting_grd                         true
% 2.97/1.00  --splitting_cvd                         false
% 2.97/1.00  --splitting_cvd_svl                     false
% 2.97/1.00  --splitting_nvd                         32
% 2.97/1.00  --sub_typing                            true
% 2.97/1.00  --prep_gs_sim                           true
% 2.97/1.00  --prep_unflatten                        true
% 2.97/1.00  --prep_res_sim                          true
% 2.97/1.00  --prep_upred                            true
% 2.97/1.00  --prep_sem_filter                       exhaustive
% 2.97/1.00  --prep_sem_filter_out                   false
% 2.97/1.00  --pred_elim                             true
% 2.97/1.00  --res_sim_input                         true
% 2.97/1.00  --eq_ax_congr_red                       true
% 2.97/1.00  --pure_diseq_elim                       true
% 2.97/1.00  --brand_transform                       false
% 2.97/1.00  --non_eq_to_eq                          false
% 2.97/1.00  --prep_def_merge                        true
% 2.97/1.00  --prep_def_merge_prop_impl              false
% 2.97/1.00  --prep_def_merge_mbd                    true
% 2.97/1.00  --prep_def_merge_tr_red                 false
% 2.97/1.00  --prep_def_merge_tr_cl                  false
% 2.97/1.00  --smt_preprocessing                     true
% 2.97/1.00  --smt_ac_axioms                         fast
% 2.97/1.00  --preprocessed_out                      false
% 2.97/1.00  --preprocessed_stats                    false
% 2.97/1.00  
% 2.97/1.00  ------ Abstraction refinement Options
% 2.97/1.00  
% 2.97/1.00  --abstr_ref                             []
% 2.97/1.00  --abstr_ref_prep                        false
% 2.97/1.00  --abstr_ref_until_sat                   false
% 2.97/1.00  --abstr_ref_sig_restrict                funpre
% 2.97/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.97/1.00  --abstr_ref_under                       []
% 2.97/1.00  
% 2.97/1.00  ------ SAT Options
% 2.97/1.00  
% 2.97/1.00  --sat_mode                              false
% 2.97/1.00  --sat_fm_restart_options                ""
% 2.97/1.00  --sat_gr_def                            false
% 2.97/1.00  --sat_epr_types                         true
% 2.97/1.00  --sat_non_cyclic_types                  false
% 2.97/1.00  --sat_finite_models                     false
% 2.97/1.00  --sat_fm_lemmas                         false
% 2.97/1.00  --sat_fm_prep                           false
% 2.97/1.00  --sat_fm_uc_incr                        true
% 2.97/1.00  --sat_out_model                         small
% 2.97/1.00  --sat_out_clauses                       false
% 2.97/1.00  
% 2.97/1.00  ------ QBF Options
% 2.97/1.00  
% 2.97/1.00  --qbf_mode                              false
% 2.97/1.00  --qbf_elim_univ                         false
% 2.97/1.00  --qbf_dom_inst                          none
% 2.97/1.00  --qbf_dom_pre_inst                      false
% 2.97/1.00  --qbf_sk_in                             false
% 2.97/1.00  --qbf_pred_elim                         true
% 2.97/1.00  --qbf_split                             512
% 2.97/1.00  
% 2.97/1.00  ------ BMC1 Options
% 2.97/1.00  
% 2.97/1.00  --bmc1_incremental                      false
% 2.97/1.00  --bmc1_axioms                           reachable_all
% 2.97/1.00  --bmc1_min_bound                        0
% 2.97/1.00  --bmc1_max_bound                        -1
% 2.97/1.00  --bmc1_max_bound_default                -1
% 2.97/1.00  --bmc1_symbol_reachability              true
% 2.97/1.00  --bmc1_property_lemmas                  false
% 2.97/1.00  --bmc1_k_induction                      false
% 2.97/1.00  --bmc1_non_equiv_states                 false
% 2.97/1.00  --bmc1_deadlock                         false
% 2.97/1.00  --bmc1_ucm                              false
% 2.97/1.00  --bmc1_add_unsat_core                   none
% 2.97/1.00  --bmc1_unsat_core_children              false
% 2.97/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.97/1.00  --bmc1_out_stat                         full
% 2.97/1.00  --bmc1_ground_init                      false
% 2.97/1.00  --bmc1_pre_inst_next_state              false
% 2.97/1.00  --bmc1_pre_inst_state                   false
% 2.97/1.00  --bmc1_pre_inst_reach_state             false
% 2.97/1.00  --bmc1_out_unsat_core                   false
% 2.97/1.00  --bmc1_aig_witness_out                  false
% 2.97/1.00  --bmc1_verbose                          false
% 2.97/1.00  --bmc1_dump_clauses_tptp                false
% 2.97/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.97/1.00  --bmc1_dump_file                        -
% 2.97/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.97/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.97/1.00  --bmc1_ucm_extend_mode                  1
% 2.97/1.00  --bmc1_ucm_init_mode                    2
% 2.97/1.00  --bmc1_ucm_cone_mode                    none
% 2.97/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.97/1.00  --bmc1_ucm_relax_model                  4
% 2.97/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.97/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.97/1.00  --bmc1_ucm_layered_model                none
% 2.97/1.00  --bmc1_ucm_max_lemma_size               10
% 2.97/1.00  
% 2.97/1.00  ------ AIG Options
% 2.97/1.00  
% 2.97/1.00  --aig_mode                              false
% 2.97/1.00  
% 2.97/1.00  ------ Instantiation Options
% 2.97/1.00  
% 2.97/1.00  --instantiation_flag                    true
% 2.97/1.00  --inst_sos_flag                         false
% 2.97/1.00  --inst_sos_phase                        true
% 2.97/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.97/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.97/1.00  --inst_lit_sel_side                     none
% 2.97/1.00  --inst_solver_per_active                1400
% 2.97/1.00  --inst_solver_calls_frac                1.
% 2.97/1.00  --inst_passive_queue_type               priority_queues
% 2.97/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.97/1.00  --inst_passive_queues_freq              [25;2]
% 2.97/1.00  --inst_dismatching                      true
% 2.97/1.00  --inst_eager_unprocessed_to_passive     true
% 2.97/1.00  --inst_prop_sim_given                   true
% 2.97/1.00  --inst_prop_sim_new                     false
% 2.97/1.00  --inst_subs_new                         false
% 2.97/1.00  --inst_eq_res_simp                      false
% 2.97/1.00  --inst_subs_given                       false
% 2.97/1.00  --inst_orphan_elimination               true
% 2.97/1.00  --inst_learning_loop_flag               true
% 2.97/1.00  --inst_learning_start                   3000
% 2.97/1.00  --inst_learning_factor                  2
% 2.97/1.00  --inst_start_prop_sim_after_learn       3
% 2.97/1.00  --inst_sel_renew                        solver
% 2.97/1.00  --inst_lit_activity_flag                true
% 2.97/1.00  --inst_restr_to_given                   false
% 2.97/1.00  --inst_activity_threshold               500
% 2.97/1.00  --inst_out_proof                        true
% 2.97/1.00  
% 2.97/1.00  ------ Resolution Options
% 2.97/1.00  
% 2.97/1.00  --resolution_flag                       false
% 2.97/1.00  --res_lit_sel                           adaptive
% 2.97/1.00  --res_lit_sel_side                      none
% 2.97/1.00  --res_ordering                          kbo
% 2.97/1.00  --res_to_prop_solver                    active
% 2.97/1.00  --res_prop_simpl_new                    false
% 2.97/1.00  --res_prop_simpl_given                  true
% 2.97/1.00  --res_passive_queue_type                priority_queues
% 2.97/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.97/1.00  --res_passive_queues_freq               [15;5]
% 2.97/1.00  --res_forward_subs                      full
% 2.97/1.00  --res_backward_subs                     full
% 2.97/1.00  --res_forward_subs_resolution           true
% 2.97/1.00  --res_backward_subs_resolution          true
% 2.97/1.00  --res_orphan_elimination                true
% 2.97/1.00  --res_time_limit                        2.
% 2.97/1.00  --res_out_proof                         true
% 2.97/1.00  
% 2.97/1.00  ------ Superposition Options
% 2.97/1.00  
% 2.97/1.00  --superposition_flag                    true
% 2.97/1.00  --sup_passive_queue_type                priority_queues
% 2.97/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.97/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.97/1.00  --demod_completeness_check              fast
% 2.97/1.00  --demod_use_ground                      true
% 2.97/1.00  --sup_to_prop_solver                    passive
% 2.97/1.00  --sup_prop_simpl_new                    true
% 2.97/1.00  --sup_prop_simpl_given                  true
% 2.97/1.00  --sup_fun_splitting                     false
% 2.97/1.00  --sup_smt_interval                      50000
% 2.97/1.00  
% 2.97/1.00  ------ Superposition Simplification Setup
% 2.97/1.00  
% 2.97/1.00  --sup_indices_passive                   []
% 2.97/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.97/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.00  --sup_full_bw                           [BwDemod]
% 2.97/1.00  --sup_immed_triv                        [TrivRules]
% 2.97/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.97/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.00  --sup_immed_bw_main                     []
% 2.97/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.97/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/1.00  
% 2.97/1.00  ------ Combination Options
% 2.97/1.00  
% 2.97/1.00  --comb_res_mult                         3
% 2.97/1.00  --comb_sup_mult                         2
% 2.97/1.00  --comb_inst_mult                        10
% 2.97/1.00  
% 2.97/1.00  ------ Debug Options
% 2.97/1.00  
% 2.97/1.00  --dbg_backtrace                         false
% 2.97/1.00  --dbg_dump_prop_clauses                 false
% 2.97/1.00  --dbg_dump_prop_clauses_file            -
% 2.97/1.00  --dbg_out_stat                          false
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  ------ Proving...
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  % SZS status Theorem for theBenchmark.p
% 2.97/1.00  
% 2.97/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.97/1.00  
% 2.97/1.00  fof(f7,axiom,(
% 2.97/1.00    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f24,plain,(
% 2.97/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 2.97/1.00    inference(ennf_transformation,[],[f7])).
% 2.97/1.00  
% 2.97/1.00  fof(f25,plain,(
% 2.97/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.97/1.00    inference(flattening,[],[f24])).
% 2.97/1.00  
% 2.97/1.00  fof(f38,plain,(
% 2.97/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.97/1.00    inference(nnf_transformation,[],[f25])).
% 2.97/1.00  
% 2.97/1.00  fof(f39,plain,(
% 2.97/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.97/1.00    inference(flattening,[],[f38])).
% 2.97/1.00  
% 2.97/1.00  fof(f40,plain,(
% 2.97/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.97/1.00    inference(rectify,[],[f39])).
% 2.97/1.00  
% 2.97/1.00  fof(f41,plain,(
% 2.97/1.00    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK1(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X1) & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0))))),
% 2.97/1.00    introduced(choice_axiom,[])).
% 2.97/1.00  
% 2.97/1.00  fof(f42,plain,(
% 2.97/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,sK1(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X1) & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.97/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f40,f41])).
% 2.97/1.00  
% 2.97/1.00  fof(f66,plain,(
% 2.97/1.00    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,sK1(X0,X1,X2,X3),X3) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f42])).
% 2.97/1.00  
% 2.97/1.00  fof(f4,axiom,(
% 2.97/1.00    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f18,plain,(
% 2.97/1.00    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 2.97/1.00    inference(ennf_transformation,[],[f4])).
% 2.97/1.00  
% 2.97/1.00  fof(f19,plain,(
% 2.97/1.00    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 2.97/1.00    inference(flattening,[],[f18])).
% 2.97/1.00  
% 2.97/1.00  fof(f51,plain,(
% 2.97/1.00    ( ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f19])).
% 2.97/1.00  
% 2.97/1.00  fof(f10,conjecture,(
% 2.97/1.00    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1)))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f11,negated_conjecture,(
% 2.97/1.00    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1)))),
% 2.97/1.00    inference(negated_conjecture,[],[f10])).
% 2.97/1.00  
% 2.97/1.00  fof(f30,plain,(
% 2.97/1.00    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)))),
% 2.97/1.00    inference(ennf_transformation,[],[f11])).
% 2.97/1.00  
% 2.97/1.00  fof(f31,plain,(
% 2.97/1.00    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 2.97/1.00    inference(flattening,[],[f30])).
% 2.97/1.00  
% 2.97/1.00  fof(f45,plain,(
% 2.97/1.00    ( ! [X0,X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) => (k12_lattice3(X0,X1,k13_lattice3(X0,X1,sK4)) != X1 & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 2.97/1.00    introduced(choice_axiom,[])).
% 2.97/1.00  
% 2.97/1.00  fof(f44,plain,(
% 2.97/1.00    ( ! [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k12_lattice3(X0,sK3,k13_lattice3(X0,sK3,X2)) != sK3 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 2.97/1.00    introduced(choice_axiom,[])).
% 2.97/1.00  
% 2.97/1.00  fof(f43,plain,(
% 2.97/1.00    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => (? [X1] : (? [X2] : (k12_lattice3(sK2,X1,k13_lattice3(sK2,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_orders_2(sK2) & v2_lattice3(sK2) & v1_lattice3(sK2) & v5_orders_2(sK2) & v3_orders_2(sK2))),
% 2.97/1.00    introduced(choice_axiom,[])).
% 2.97/1.00  
% 2.97/1.00  fof(f46,plain,(
% 2.97/1.00    ((k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 & m1_subset_1(sK4,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_orders_2(sK2) & v2_lattice3(sK2) & v1_lattice3(sK2) & v5_orders_2(sK2) & v3_orders_2(sK2)),
% 2.97/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f31,f45,f44,f43])).
% 2.97/1.00  
% 2.97/1.00  fof(f72,plain,(
% 2.97/1.00    v2_lattice3(sK2)),
% 2.97/1.00    inference(cnf_transformation,[],[f46])).
% 2.97/1.00  
% 2.97/1.00  fof(f70,plain,(
% 2.97/1.00    v5_orders_2(sK2)),
% 2.97/1.00    inference(cnf_transformation,[],[f46])).
% 2.97/1.00  
% 2.97/1.00  fof(f73,plain,(
% 2.97/1.00    l1_orders_2(sK2)),
% 2.97/1.00    inference(cnf_transformation,[],[f46])).
% 2.97/1.00  
% 2.97/1.00  fof(f64,plain,(
% 2.97/1.00    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | r1_orders_2(X0,sK1(X0,X1,X2,X3),X1) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f42])).
% 2.97/1.00  
% 2.97/1.00  fof(f75,plain,(
% 2.97/1.00    m1_subset_1(sK4,u1_struct_0(sK2))),
% 2.97/1.00    inference(cnf_transformation,[],[f46])).
% 2.97/1.00  
% 2.97/1.00  fof(f74,plain,(
% 2.97/1.00    m1_subset_1(sK3,u1_struct_0(sK2))),
% 2.97/1.00    inference(cnf_transformation,[],[f46])).
% 2.97/1.00  
% 2.97/1.00  fof(f5,axiom,(
% 2.97/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f20,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 2.97/1.00    inference(ennf_transformation,[],[f5])).
% 2.97/1.00  
% 2.97/1.00  fof(f21,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 2.97/1.00    inference(flattening,[],[f20])).
% 2.97/1.00  
% 2.97/1.00  fof(f52,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f21])).
% 2.97/1.00  
% 2.97/1.00  fof(f8,axiom,(
% 2.97/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f26,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 2.97/1.00    inference(ennf_transformation,[],[f8])).
% 2.97/1.00  
% 2.97/1.00  fof(f27,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 2.97/1.00    inference(flattening,[],[f26])).
% 2.97/1.00  
% 2.97/1.00  fof(f67,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f27])).
% 2.97/1.00  
% 2.97/1.00  fof(f9,axiom,(
% 2.97/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f28,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 2.97/1.00    inference(ennf_transformation,[],[f9])).
% 2.97/1.00  
% 2.97/1.00  fof(f29,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 2.97/1.00    inference(flattening,[],[f28])).
% 2.97/1.00  
% 2.97/1.00  fof(f68,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f29])).
% 2.97/1.00  
% 2.97/1.00  fof(f71,plain,(
% 2.97/1.00    v1_lattice3(sK2)),
% 2.97/1.00    inference(cnf_transformation,[],[f46])).
% 2.97/1.00  
% 2.97/1.00  fof(f76,plain,(
% 2.97/1.00    k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3),
% 2.97/1.00    inference(cnf_transformation,[],[f46])).
% 2.97/1.00  
% 2.97/1.00  fof(f6,axiom,(
% 2.97/1.00    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f22,plain,(
% 2.97/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 2.97/1.00    inference(ennf_transformation,[],[f6])).
% 2.97/1.00  
% 2.97/1.00  fof(f23,plain,(
% 2.97/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.97/1.00    inference(flattening,[],[f22])).
% 2.97/1.00  
% 2.97/1.00  fof(f33,plain,(
% 2.97/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3))) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.97/1.00    inference(nnf_transformation,[],[f23])).
% 2.97/1.00  
% 2.97/1.00  fof(f34,plain,(
% 2.97/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.97/1.00    inference(flattening,[],[f33])).
% 2.97/1.00  
% 2.97/1.00  fof(f35,plain,(
% 2.97/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.97/1.00    inference(rectify,[],[f34])).
% 2.97/1.00  
% 2.97/1.00  fof(f36,plain,(
% 2.97/1.00    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,X3,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))))),
% 2.97/1.00    introduced(choice_axiom,[])).
% 2.97/1.00  
% 2.97/1.00  fof(f37,plain,(
% 2.97/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,X3,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.97/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).
% 2.97/1.00  
% 2.97/1.00  fof(f53,plain,(
% 2.97/1.00    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X1,X3) | k10_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f37])).
% 2.97/1.00  
% 2.97/1.00  fof(f79,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.97/1.00    inference(equality_resolution,[],[f53])).
% 2.97/1.00  
% 2.97/1.00  fof(f3,axiom,(
% 2.97/1.00    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f16,plain,(
% 2.97/1.00    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 2.97/1.00    inference(ennf_transformation,[],[f3])).
% 2.97/1.00  
% 2.97/1.00  fof(f17,plain,(
% 2.97/1.00    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 2.97/1.00    inference(flattening,[],[f16])).
% 2.97/1.00  
% 2.97/1.00  fof(f50,plain,(
% 2.97/1.00    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f17])).
% 2.97/1.00  
% 2.97/1.00  fof(f2,axiom,(
% 2.97/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => r3_orders_2(X0,X1,X1))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f14,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.97/1.00    inference(ennf_transformation,[],[f2])).
% 2.97/1.00  
% 2.97/1.00  fof(f15,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.97/1.00    inference(flattening,[],[f14])).
% 2.97/1.00  
% 2.97/1.00  fof(f49,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f15])).
% 2.97/1.00  
% 2.97/1.00  fof(f69,plain,(
% 2.97/1.00    v3_orders_2(sK2)),
% 2.97/1.00    inference(cnf_transformation,[],[f46])).
% 2.97/1.00  
% 2.97/1.00  fof(f1,axiom,(
% 2.97/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f12,plain,(
% 2.97/1.00    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.97/1.00    inference(ennf_transformation,[],[f1])).
% 2.97/1.00  
% 2.97/1.00  fof(f13,plain,(
% 2.97/1.00    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.97/1.00    inference(flattening,[],[f12])).
% 2.97/1.00  
% 2.97/1.00  fof(f32,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.97/1.00    inference(nnf_transformation,[],[f13])).
% 2.97/1.00  
% 2.97/1.00  fof(f47,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f32])).
% 2.97/1.00  
% 2.97/1.00  cnf(c_13,plain,
% 2.97/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 2.97/1.00      | ~ r1_orders_2(X0,X1,X3)
% 2.97/1.00      | ~ r1_orders_2(X0,sK1(X0,X3,X2,X1),X1)
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | ~ v5_orders_2(X0)
% 2.97/1.00      | ~ v2_lattice3(X0)
% 2.97/1.00      | v2_struct_0(X0)
% 2.97/1.00      | ~ l1_orders_2(X0)
% 2.97/1.00      | k11_lattice3(X0,X3,X2) = X1 ),
% 2.97/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_4,plain,
% 2.97/1.00      ( ~ v2_lattice3(X0) | ~ v2_struct_0(X0) | ~ l1_orders_2(X0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_201,plain,
% 2.97/1.00      ( ~ v2_lattice3(X0)
% 2.97/1.00      | ~ v5_orders_2(X0)
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.00      | ~ r1_orders_2(X0,sK1(X0,X3,X2,X1),X1)
% 2.97/1.00      | ~ r1_orders_2(X0,X1,X3)
% 2.97/1.00      | ~ r1_orders_2(X0,X1,X2)
% 2.97/1.00      | ~ l1_orders_2(X0)
% 2.97/1.00      | k11_lattice3(X0,X3,X2) = X1 ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_13,c_4]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_202,plain,
% 2.97/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 2.97/1.00      | ~ r1_orders_2(X0,X1,X3)
% 2.97/1.00      | ~ r1_orders_2(X0,sK1(X0,X3,X2,X1),X1)
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.97/1.00      | ~ v5_orders_2(X0)
% 2.97/1.00      | ~ v2_lattice3(X0)
% 2.97/1.00      | ~ l1_orders_2(X0)
% 2.97/1.00      | k11_lattice3(X0,X3,X2) = X1 ),
% 2.97/1.00      inference(renaming,[status(thm)],[c_201]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_26,negated_conjecture,
% 2.97/1.00      ( v2_lattice3(sK2) ),
% 2.97/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_770,plain,
% 2.97/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 2.97/1.00      | ~ r1_orders_2(X0,X1,X3)
% 2.97/1.00      | ~ r1_orders_2(X0,sK1(X0,X3,X2,X1),X1)
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.97/1.00      | ~ v5_orders_2(X0)
% 2.97/1.00      | ~ l1_orders_2(X0)
% 2.97/1.00      | k11_lattice3(X0,X3,X2) = X1
% 2.97/1.00      | sK2 != X0 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_202,c_26]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_771,plain,
% 2.97/1.00      ( ~ r1_orders_2(sK2,X0,X1)
% 2.97/1.00      | ~ r1_orders_2(sK2,X0,X2)
% 2.97/1.00      | ~ r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X0)
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 2.97/1.00      | ~ v5_orders_2(sK2)
% 2.97/1.00      | ~ l1_orders_2(sK2)
% 2.97/1.00      | k11_lattice3(sK2,X2,X1) = X0 ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_770]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_28,negated_conjecture,
% 2.97/1.00      ( v5_orders_2(sK2) ),
% 2.97/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_25,negated_conjecture,
% 2.97/1.00      ( l1_orders_2(sK2) ),
% 2.97/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_775,plain,
% 2.97/1.00      ( ~ r1_orders_2(sK2,X0,X1)
% 2.97/1.00      | ~ r1_orders_2(sK2,X0,X2)
% 2.97/1.00      | ~ r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X0)
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 2.97/1.00      | k11_lattice3(sK2,X2,X1) = X0 ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_771,c_28,c_25]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_776,plain,
% 2.97/1.00      ( ~ r1_orders_2(sK2,X0,X1)
% 2.97/1.00      | ~ r1_orders_2(sK2,X0,X2)
% 2.97/1.00      | ~ r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X0)
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | k11_lattice3(sK2,X2,X1) = X0 ),
% 2.97/1.00      inference(renaming,[status(thm)],[c_775]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1222,plain,
% 2.97/1.00      ( ~ r1_orders_2(sK2,X0_48,X1_48)
% 2.97/1.00      | ~ r1_orders_2(sK2,X0_48,X2_48)
% 2.97/1.00      | ~ r1_orders_2(sK2,sK1(sK2,X2_48,X1_48,X0_48),X0_48)
% 2.97/1.00      | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X2_48,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
% 2.97/1.00      | k11_lattice3(sK2,X2_48,X1_48) = X0_48 ),
% 2.97/1.00      inference(subtyping,[status(esa)],[c_776]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_6775,plain,
% 2.97/1.00      ( ~ r1_orders_2(sK2,sK1(sK2,X0_48,k10_lattice3(sK2,sK3,sK4),sK3),sK3)
% 2.97/1.00      | ~ r1_orders_2(sK2,sK3,X0_48)
% 2.97/1.00      | ~ r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK4))
% 2.97/1.00      | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(k10_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.97/1.00      | k11_lattice3(sK2,X0_48,k10_lattice3(sK2,sK3,sK4)) = sK3 ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_1222]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_6792,plain,
% 2.97/1.00      ( ~ r1_orders_2(sK2,sK1(sK2,sK3,k10_lattice3(sK2,sK3,sK4),sK3),sK3)
% 2.97/1.00      | ~ r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK4))
% 2.97/1.00      | ~ r1_orders_2(sK2,sK3,sK3)
% 2.97/1.00      | ~ m1_subset_1(k10_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.97/1.00      | k11_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,sK4)) = sK3 ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_6775]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_15,plain,
% 2.97/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 2.97/1.00      | ~ r1_orders_2(X0,X1,X3)
% 2.97/1.00      | r1_orders_2(X0,sK1(X0,X3,X2,X1),X3)
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | ~ v5_orders_2(X0)
% 2.97/1.00      | ~ v2_lattice3(X0)
% 2.97/1.00      | v2_struct_0(X0)
% 2.97/1.00      | ~ l1_orders_2(X0)
% 2.97/1.00      | k11_lattice3(X0,X3,X2) = X1 ),
% 2.97/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_189,plain,
% 2.97/1.00      ( ~ v2_lattice3(X0)
% 2.97/1.00      | ~ v5_orders_2(X0)
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.00      | r1_orders_2(X0,sK1(X0,X3,X2,X1),X3)
% 2.97/1.00      | ~ r1_orders_2(X0,X1,X3)
% 2.97/1.00      | ~ r1_orders_2(X0,X1,X2)
% 2.97/1.00      | ~ l1_orders_2(X0)
% 2.97/1.00      | k11_lattice3(X0,X3,X2) = X1 ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_15,c_4]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_190,plain,
% 2.97/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 2.97/1.00      | ~ r1_orders_2(X0,X1,X3)
% 2.97/1.00      | r1_orders_2(X0,sK1(X0,X3,X2,X1),X3)
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.97/1.00      | ~ v5_orders_2(X0)
% 2.97/1.00      | ~ v2_lattice3(X0)
% 2.97/1.00      | ~ l1_orders_2(X0)
% 2.97/1.00      | k11_lattice3(X0,X3,X2) = X1 ),
% 2.97/1.00      inference(renaming,[status(thm)],[c_189]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_836,plain,
% 2.97/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 2.97/1.00      | ~ r1_orders_2(X0,X1,X3)
% 2.97/1.00      | r1_orders_2(X0,sK1(X0,X3,X2,X1),X3)
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.97/1.00      | ~ v5_orders_2(X0)
% 2.97/1.00      | ~ l1_orders_2(X0)
% 2.97/1.00      | k11_lattice3(X0,X3,X2) = X1
% 2.97/1.00      | sK2 != X0 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_190,c_26]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_837,plain,
% 2.97/1.00      ( ~ r1_orders_2(sK2,X0,X1)
% 2.97/1.00      | ~ r1_orders_2(sK2,X0,X2)
% 2.97/1.00      | r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X2)
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 2.97/1.00      | ~ v5_orders_2(sK2)
% 2.97/1.00      | ~ l1_orders_2(sK2)
% 2.97/1.00      | k11_lattice3(sK2,X2,X1) = X0 ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_836]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_839,plain,
% 2.97/1.00      ( ~ r1_orders_2(sK2,X0,X1)
% 2.97/1.00      | ~ r1_orders_2(sK2,X0,X2)
% 2.97/1.00      | r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X2)
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 2.97/1.00      | k11_lattice3(sK2,X2,X1) = X0 ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_837,c_28,c_25]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_840,plain,
% 2.97/1.00      ( ~ r1_orders_2(sK2,X0,X1)
% 2.97/1.00      | ~ r1_orders_2(sK2,X0,X2)
% 2.97/1.00      | r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X2)
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | k11_lattice3(sK2,X2,X1) = X0 ),
% 2.97/1.00      inference(renaming,[status(thm)],[c_839]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1220,plain,
% 2.97/1.00      ( ~ r1_orders_2(sK2,X0_48,X1_48)
% 2.97/1.00      | ~ r1_orders_2(sK2,X0_48,X2_48)
% 2.97/1.00      | r1_orders_2(sK2,sK1(sK2,X2_48,X1_48,X0_48),X2_48)
% 2.97/1.00      | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X2_48,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
% 2.97/1.00      | k11_lattice3(sK2,X2_48,X1_48) = X0_48 ),
% 2.97/1.00      inference(subtyping,[status(esa)],[c_840]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_6777,plain,
% 2.97/1.00      ( r1_orders_2(sK2,sK1(sK2,X0_48,k10_lattice3(sK2,sK3,sK4),sK3),X0_48)
% 2.97/1.00      | ~ r1_orders_2(sK2,sK3,X0_48)
% 2.97/1.00      | ~ r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK4))
% 2.97/1.00      | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(k10_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.97/1.00      | k11_lattice3(sK2,X0_48,k10_lattice3(sK2,sK3,sK4)) = sK3 ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_1220]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_6784,plain,
% 2.97/1.00      ( r1_orders_2(sK2,sK1(sK2,sK3,k10_lattice3(sK2,sK3,sK4),sK3),sK3)
% 2.97/1.00      | ~ r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK4))
% 2.97/1.00      | ~ r1_orders_2(sK2,sK3,sK3)
% 2.97/1.00      | ~ m1_subset_1(k10_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.97/1.00      | k11_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,sK4)) = sK3 ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_6777]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_23,negated_conjecture,
% 2.97/1.00      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 2.97/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1230,negated_conjecture,
% 2.97/1.00      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 2.97/1.00      inference(subtyping,[status(esa)],[c_23]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1612,plain,
% 2.97/1.00      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_1230]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_24,negated_conjecture,
% 2.97/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.97/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1229,negated_conjecture,
% 2.97/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.97/1.00      inference(subtyping,[status(esa)],[c_24]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1613,plain,
% 2.97/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_1229]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_5,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.97/1.00      | m1_subset_1(k10_lattice3(X1,X2,X0),u1_struct_0(X1))
% 2.97/1.00      | ~ l1_orders_2(X1) ),
% 2.97/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1050,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.97/1.00      | m1_subset_1(k10_lattice3(X1,X2,X0),u1_struct_0(X1))
% 2.97/1.00      | sK2 != X1 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_25]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1051,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_1050]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1214,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0_48,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
% 2.97/1.00      | m1_subset_1(k10_lattice3(sK2,X0_48,X1_48),u1_struct_0(sK2)) ),
% 2.97/1.00      inference(subtyping,[status(esa)],[c_1051]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1630,plain,
% 2.97/1.00      ( m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
% 2.97/1.00      | m1_subset_1(X1_48,u1_struct_0(sK2)) != iProver_top
% 2.97/1.00      | m1_subset_1(k10_lattice3(sK2,X0_48,X1_48),u1_struct_0(sK2)) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_1214]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_20,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.97/1.00      | ~ v5_orders_2(X1)
% 2.97/1.00      | ~ v2_lattice3(X1)
% 2.97/1.00      | ~ l1_orders_2(X1)
% 2.97/1.00      | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_975,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.97/1.00      | ~ v5_orders_2(X1)
% 2.97/1.00      | ~ l1_orders_2(X1)
% 2.97/1.00      | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0)
% 2.97/1.00      | sK2 != X1 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_26]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_976,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | ~ v5_orders_2(sK2)
% 2.97/1.00      | ~ l1_orders_2(sK2)
% 2.97/1.00      | k12_lattice3(sK2,X0,X1) = k11_lattice3(sK2,X0,X1) ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_975]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_980,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | k12_lattice3(sK2,X0,X1) = k11_lattice3(sK2,X0,X1) ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_976,c_28,c_25]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_981,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | k12_lattice3(sK2,X1,X0) = k11_lattice3(sK2,X1,X0) ),
% 2.97/1.00      inference(renaming,[status(thm)],[c_980]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1215,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0_48,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
% 2.97/1.00      | k12_lattice3(sK2,X1_48,X0_48) = k11_lattice3(sK2,X1_48,X0_48) ),
% 2.97/1.00      inference(subtyping,[status(esa)],[c_981]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1629,plain,
% 2.97/1.00      ( k12_lattice3(sK2,X0_48,X1_48) = k11_lattice3(sK2,X0_48,X1_48)
% 2.97/1.00      | m1_subset_1(X1_48,u1_struct_0(sK2)) != iProver_top
% 2.97/1.00      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_1215]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2251,plain,
% 2.97/1.00      ( k12_lattice3(sK2,sK3,X0_48) = k11_lattice3(sK2,sK3,X0_48)
% 2.97/1.00      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_1613,c_1629]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2765,plain,
% 2.97/1.00      ( k12_lattice3(sK2,sK3,k10_lattice3(sK2,X0_48,X1_48)) = k11_lattice3(sK2,sK3,k10_lattice3(sK2,X0_48,X1_48))
% 2.97/1.00      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
% 2.97/1.00      | m1_subset_1(X1_48,u1_struct_0(sK2)) != iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_1630,c_2251]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2844,plain,
% 2.97/1.00      ( k12_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,X0_48)) = k11_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,X0_48))
% 2.97/1.00      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_1613,c_2765]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_3199,plain,
% 2.97/1.00      ( k12_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,sK4)) = k11_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,sK4)) ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_1612,c_2844]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_21,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.97/1.00      | ~ v5_orders_2(X1)
% 2.97/1.00      | ~ v1_lattice3(X1)
% 2.97/1.00      | ~ l1_orders_2(X1)
% 2.97/1.00      | k13_lattice3(X1,X2,X0) = k10_lattice3(X1,X2,X0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_27,negated_conjecture,
% 2.97/1.00      ( v1_lattice3(sK2) ),
% 2.97/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_695,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.97/1.00      | ~ v5_orders_2(X1)
% 2.97/1.00      | ~ l1_orders_2(X1)
% 2.97/1.00      | k13_lattice3(X1,X2,X0) = k10_lattice3(X1,X2,X0)
% 2.97/1.00      | sK2 != X1 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_696,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | ~ v5_orders_2(sK2)
% 2.97/1.00      | ~ l1_orders_2(sK2)
% 2.97/1.00      | k13_lattice3(sK2,X0,X1) = k10_lattice3(sK2,X0,X1) ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_695]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_700,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | k13_lattice3(sK2,X0,X1) = k10_lattice3(sK2,X0,X1) ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_696,c_28,c_25]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_701,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | k13_lattice3(sK2,X1,X0) = k10_lattice3(sK2,X1,X0) ),
% 2.97/1.00      inference(renaming,[status(thm)],[c_700]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1223,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0_48,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
% 2.97/1.00      | k13_lattice3(sK2,X1_48,X0_48) = k10_lattice3(sK2,X1_48,X0_48) ),
% 2.97/1.00      inference(subtyping,[status(esa)],[c_701]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1621,plain,
% 2.97/1.00      ( k13_lattice3(sK2,X0_48,X1_48) = k10_lattice3(sK2,X0_48,X1_48)
% 2.97/1.00      | m1_subset_1(X1_48,u1_struct_0(sK2)) != iProver_top
% 2.97/1.00      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_1223]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1892,plain,
% 2.97/1.00      ( k13_lattice3(sK2,sK3,X0_48) = k10_lattice3(sK2,sK3,X0_48)
% 2.97/1.00      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_1613,c_1621]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2000,plain,
% 2.97/1.00      ( k13_lattice3(sK2,sK3,sK4) = k10_lattice3(sK2,sK3,sK4) ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_1612,c_1892]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_22,negated_conjecture,
% 2.97/1.00      ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
% 2.97/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1231,negated_conjecture,
% 2.97/1.00      ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
% 2.97/1.00      inference(subtyping,[status(esa)],[c_22]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2153,plain,
% 2.97/1.00      ( k12_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,sK4)) != sK3 ),
% 2.97/1.00      inference(demodulation,[status(thm)],[c_2000,c_1231]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_3286,plain,
% 2.97/1.00      ( k11_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,sK4)) != sK3 ),
% 2.97/1.00      inference(demodulation,[status(thm)],[c_3199,c_2153]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_12,plain,
% 2.97/1.00      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.97/1.00      | ~ v5_orders_2(X0)
% 2.97/1.00      | ~ v1_lattice3(X0)
% 2.97/1.00      | v2_struct_0(X0)
% 2.97/1.00      | ~ l1_orders_2(X0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_3,plain,
% 2.97/1.00      ( ~ v1_lattice3(X0) | ~ v2_struct_0(X0) | ~ l1_orders_2(X0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_208,plain,
% 2.97/1.00      ( ~ v1_lattice3(X0)
% 2.97/1.00      | ~ v5_orders_2(X0)
% 2.97/1.00      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.00      | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 2.97/1.00      | ~ l1_orders_2(X0) ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_12,c_3]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_209,plain,
% 2.97/1.00      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.97/1.00      | ~ v5_orders_2(X0)
% 2.97/1.00      | ~ v1_lattice3(X0)
% 2.97/1.00      | ~ l1_orders_2(X0) ),
% 2.97/1.00      inference(renaming,[status(thm)],[c_208]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_675,plain,
% 2.97/1.00      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.97/1.00      | ~ v5_orders_2(X0)
% 2.97/1.00      | ~ l1_orders_2(X0)
% 2.97/1.00      | sK2 != X0 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_209,c_27]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_676,plain,
% 2.97/1.00      ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2))
% 2.97/1.00      | ~ v5_orders_2(sK2)
% 2.97/1.00      | ~ l1_orders_2(sK2) ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_675]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_678,plain,
% 2.97/1.00      ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_676,c_28,c_25]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_679,plain,
% 2.97/1.00      ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
% 2.97/1.00      inference(renaming,[status(thm)],[c_678]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1068,plain,
% 2.97/1.00      ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 2.97/1.00      inference(backward_subsumption_resolution,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_1051,c_679]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1213,plain,
% 2.97/1.00      ( r1_orders_2(sK2,X0_48,k10_lattice3(sK2,X0_48,X1_48))
% 2.97/1.00      | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X0_48,u1_struct_0(sK2)) ),
% 2.97/1.00      inference(subtyping,[status(esa)],[c_1068]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2448,plain,
% 2.97/1.00      ( r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK4))
% 2.97/1.00      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_1213]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2235,plain,
% 2.97/1.00      ( m1_subset_1(k10_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_1214]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2,plain,
% 2.97/1.00      ( r3_orders_2(X0,X1,X1)
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | v2_struct_0(X0)
% 2.97/1.00      | ~ v3_orders_2(X0)
% 2.97/1.00      | ~ l1_orders_2(X0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_29,negated_conjecture,
% 2.97/1.00      ( v3_orders_2(sK2) ),
% 2.97/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_387,plain,
% 2.97/1.00      ( r3_orders_2(X0,X1,X1)
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | v2_struct_0(X0)
% 2.97/1.00      | ~ l1_orders_2(X0)
% 2.97/1.00      | sK2 != X0 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_29]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_388,plain,
% 2.97/1.00      ( r3_orders_2(sK2,X0,X0)
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | v2_struct_0(sK2)
% 2.97/1.00      | ~ l1_orders_2(sK2) ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_387]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_81,plain,
% 2.97/1.00      ( ~ v2_lattice3(sK2) | ~ v2_struct_0(sK2) | ~ l1_orders_2(sK2) ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_392,plain,
% 2.97/1.00      ( r3_orders_2(sK2,X0,X0)
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_388,c_26,c_25,c_81]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_393,plain,
% 2.97/1.00      ( r3_orders_2(sK2,X0,X0)
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 2.97/1.00      inference(renaming,[status(thm)],[c_392]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1,plain,
% 2.97/1.00      ( r1_orders_2(X0,X1,X2)
% 2.97/1.00      | ~ r3_orders_2(X0,X1,X2)
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | v2_struct_0(X0)
% 2.97/1.00      | ~ v3_orders_2(X0)
% 2.97/1.00      | ~ l1_orders_2(X0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_408,plain,
% 2.97/1.00      ( r1_orders_2(X0,X1,X2)
% 2.97/1.00      | ~ r3_orders_2(X0,X1,X2)
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | v2_struct_0(X0)
% 2.97/1.00      | ~ l1_orders_2(X0)
% 2.97/1.00      | sK2 != X0 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_29]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_409,plain,
% 2.97/1.00      ( r1_orders_2(sK2,X0,X1)
% 2.97/1.00      | ~ r3_orders_2(sK2,X0,X1)
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | v2_struct_0(sK2)
% 2.97/1.00      | ~ l1_orders_2(sK2) ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_408]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_413,plain,
% 2.97/1.00      ( r1_orders_2(sK2,X0,X1)
% 2.97/1.00      | ~ r3_orders_2(sK2,X0,X1)
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_409,c_26,c_25,c_81]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_414,plain,
% 2.97/1.00      ( r1_orders_2(sK2,X0,X1)
% 2.97/1.00      | ~ r3_orders_2(sK2,X0,X1)
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 2.97/1.00      inference(renaming,[status(thm)],[c_413]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_471,plain,
% 2.97/1.00      ( r1_orders_2(sK2,X0,X1)
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | X0 != X3
% 2.97/1.00      | X1 != X3
% 2.97/1.00      | sK2 != sK2 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_393,c_414]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_472,plain,
% 2.97/1.00      ( r1_orders_2(sK2,X0,X0)
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_471]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1228,plain,
% 2.97/1.00      ( r1_orders_2(sK2,X0_48,X0_48)
% 2.97/1.00      | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X0_48,u1_struct_0(sK2)) ),
% 2.97/1.00      inference(subtyping,[status(esa)],[c_472]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1232,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0_48,u1_struct_0(sK2)) | ~ sP0_iProver_split ),
% 2.97/1.00      inference(splitting,
% 2.97/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.97/1.00                [c_1228]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1255,plain,
% 2.97/1.00      ( ~ m1_subset_1(sK3,u1_struct_0(sK2)) | ~ sP0_iProver_split ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_1232]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1233,plain,
% 2.97/1.00      ( r1_orders_2(sK2,X0_48,X0_48)
% 2.97/1.00      | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
% 2.97/1.00      | ~ sP1_iProver_split ),
% 2.97/1.00      inference(splitting,
% 2.97/1.00                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.97/1.00                [c_1228]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1252,plain,
% 2.97/1.00      ( r1_orders_2(sK2,sK3,sK3)
% 2.97/1.00      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.97/1.00      | ~ sP1_iProver_split ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_1233]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1234,plain,
% 2.97/1.00      ( sP1_iProver_split | sP0_iProver_split ),
% 2.97/1.00      inference(splitting,
% 2.97/1.00                [splitting(split),new_symbols(definition,[])],
% 2.97/1.00                [c_1228]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(contradiction,plain,
% 2.97/1.00      ( $false ),
% 2.97/1.00      inference(minisat,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_6792,c_6784,c_3286,c_2448,c_2235,c_1255,c_1252,c_1234,
% 2.97/1.00                 c_23,c_24]) ).
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.97/1.00  
% 2.97/1.00  ------                               Statistics
% 2.97/1.00  
% 2.97/1.00  ------ General
% 2.97/1.00  
% 2.97/1.00  abstr_ref_over_cycles:                  0
% 2.97/1.00  abstr_ref_under_cycles:                 0
% 2.97/1.00  gc_basic_clause_elim:                   0
% 2.97/1.00  forced_gc_time:                         0
% 2.97/1.00  parsing_time:                           0.011
% 2.97/1.00  unif_index_cands_time:                  0.
% 2.97/1.00  unif_index_add_time:                    0.
% 2.97/1.00  orderings_time:                         0.
% 2.97/1.00  out_proof_time:                         0.013
% 2.97/1.00  total_time:                             0.261
% 2.97/1.00  num_of_symbols:                         52
% 2.97/1.00  num_of_terms:                           7327
% 2.97/1.00  
% 2.97/1.00  ------ Preprocessing
% 2.97/1.00  
% 2.97/1.00  num_of_splits:                          2
% 2.97/1.00  num_of_split_atoms:                     2
% 2.97/1.00  num_of_reused_defs:                     0
% 2.97/1.00  num_eq_ax_congr_red:                    48
% 2.97/1.00  num_of_sem_filtered_clauses:            3
% 2.97/1.00  num_of_subtypes:                        3
% 2.97/1.00  monotx_restored_types:                  0
% 2.97/1.00  sat_num_of_epr_types:                   0
% 2.97/1.00  sat_num_of_non_cyclic_types:            0
% 2.97/1.00  sat_guarded_non_collapsed_types:        1
% 2.97/1.00  num_pure_diseq_elim:                    0
% 2.97/1.00  simp_replaced_by:                       0
% 2.97/1.00  res_preprocessed:                       108
% 2.97/1.00  prep_upred:                             0
% 2.97/1.00  prep_unflattend:                        22
% 2.97/1.00  smt_new_axioms:                         0
% 2.97/1.00  pred_elim_cands:                        2
% 2.97/1.00  pred_elim:                              7
% 2.97/1.00  pred_elim_cl:                           9
% 2.97/1.00  pred_elim_cycles:                       9
% 2.97/1.00  merged_defs:                            0
% 2.97/1.00  merged_defs_ncl:                        0
% 2.97/1.00  bin_hyper_res:                          0
% 2.97/1.00  prep_cycles:                            4
% 2.97/1.00  pred_elim_time:                         0.023
% 2.97/1.00  splitting_time:                         0.
% 2.97/1.00  sem_filter_time:                        0.
% 2.97/1.00  monotx_time:                            0.
% 2.97/1.00  subtype_inf_time:                       0.
% 2.97/1.00  
% 2.97/1.00  ------ Problem properties
% 2.97/1.00  
% 2.97/1.00  clauses:                                23
% 2.97/1.00  conjectures:                            3
% 2.97/1.00  epr:                                    1
% 2.97/1.00  horn:                                   16
% 2.97/1.00  ground:                                 4
% 2.97/1.00  unary:                                  3
% 2.97/1.00  binary:                                 2
% 2.97/1.00  lits:                                   102
% 2.97/1.00  lits_eq:                                11
% 2.97/1.00  fd_pure:                                0
% 2.97/1.00  fd_pseudo:                              0
% 2.97/1.00  fd_cond:                                0
% 2.97/1.00  fd_pseudo_cond:                         8
% 2.97/1.00  ac_symbols:                             0
% 2.97/1.00  
% 2.97/1.00  ------ Propositional Solver
% 2.97/1.00  
% 2.97/1.00  prop_solver_calls:                      29
% 2.97/1.00  prop_fast_solver_calls:                 1586
% 2.97/1.00  smt_solver_calls:                       0
% 2.97/1.00  smt_fast_solver_calls:                  0
% 2.97/1.00  prop_num_of_clauses:                    2136
% 2.97/1.00  prop_preprocess_simplified:             5625
% 2.97/1.00  prop_fo_subsumed:                       57
% 2.97/1.00  prop_solver_time:                       0.
% 2.97/1.00  smt_solver_time:                        0.
% 2.97/1.00  smt_fast_solver_time:                   0.
% 2.97/1.00  prop_fast_solver_time:                  0.
% 2.97/1.00  prop_unsat_core_time:                   0.
% 2.97/1.00  
% 2.97/1.00  ------ QBF
% 2.97/1.00  
% 2.97/1.00  qbf_q_res:                              0
% 2.97/1.00  qbf_num_tautologies:                    0
% 2.97/1.00  qbf_prep_cycles:                        0
% 2.97/1.00  
% 2.97/1.00  ------ BMC1
% 2.97/1.00  
% 2.97/1.00  bmc1_current_bound:                     -1
% 2.97/1.00  bmc1_last_solved_bound:                 -1
% 2.97/1.00  bmc1_unsat_core_size:                   -1
% 2.97/1.00  bmc1_unsat_core_parents_size:           -1
% 2.97/1.00  bmc1_merge_next_fun:                    0
% 2.97/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.97/1.00  
% 2.97/1.00  ------ Instantiation
% 2.97/1.00  
% 2.97/1.00  inst_num_of_clauses:                    595
% 2.97/1.00  inst_num_in_passive:                    161
% 2.97/1.00  inst_num_in_active:                     312
% 2.97/1.00  inst_num_in_unprocessed:                121
% 2.97/1.00  inst_num_of_loops:                      346
% 2.97/1.00  inst_num_of_learning_restarts:          0
% 2.97/1.00  inst_num_moves_active_passive:          28
% 2.97/1.00  inst_lit_activity:                      0
% 2.97/1.00  inst_lit_activity_moves:                0
% 2.97/1.00  inst_num_tautologies:                   0
% 2.97/1.00  inst_num_prop_implied:                  0
% 2.97/1.00  inst_num_existing_simplified:           0
% 2.97/1.00  inst_num_eq_res_simplified:             0
% 2.97/1.00  inst_num_child_elim:                    0
% 2.97/1.00  inst_num_of_dismatching_blockings:      258
% 2.97/1.00  inst_num_of_non_proper_insts:           634
% 2.97/1.00  inst_num_of_duplicates:                 0
% 2.97/1.00  inst_inst_num_from_inst_to_res:         0
% 2.97/1.00  inst_dismatching_checking_time:         0.
% 2.97/1.00  
% 2.97/1.00  ------ Resolution
% 2.97/1.00  
% 2.97/1.00  res_num_of_clauses:                     0
% 2.97/1.00  res_num_in_passive:                     0
% 2.97/1.00  res_num_in_active:                      0
% 2.97/1.00  res_num_of_loops:                       112
% 2.97/1.00  res_forward_subset_subsumed:            57
% 2.97/1.00  res_backward_subset_subsumed:           0
% 2.97/1.00  res_forward_subsumed:                   0
% 2.97/1.00  res_backward_subsumed:                  0
% 2.97/1.00  res_forward_subsumption_resolution:     0
% 2.97/1.00  res_backward_subsumption_resolution:    3
% 2.97/1.00  res_clause_to_clause_subsumption:       789
% 2.97/1.00  res_orphan_elimination:                 0
% 2.97/1.00  res_tautology_del:                      75
% 2.97/1.00  res_num_eq_res_simplified:              0
% 2.97/1.00  res_num_sel_changes:                    0
% 2.97/1.00  res_moves_from_active_to_pass:          0
% 2.97/1.00  
% 2.97/1.00  ------ Superposition
% 2.97/1.00  
% 2.97/1.00  sup_time_total:                         0.
% 2.97/1.00  sup_time_generating:                    0.
% 2.97/1.00  sup_time_sim_full:                      0.
% 2.97/1.00  sup_time_sim_immed:                     0.
% 2.97/1.00  
% 2.97/1.00  sup_num_of_clauses:                     128
% 2.97/1.00  sup_num_in_active:                      66
% 2.97/1.00  sup_num_in_passive:                     62
% 2.97/1.00  sup_num_of_loops:                       68
% 2.97/1.00  sup_fw_superposition:                   64
% 2.97/1.00  sup_bw_superposition:                   41
% 2.97/1.00  sup_immediate_simplified:               0
% 2.97/1.00  sup_given_eliminated:                   0
% 2.97/1.00  comparisons_done:                       0
% 2.97/1.00  comparisons_avoided:                    0
% 2.97/1.00  
% 2.97/1.00  ------ Simplifications
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  sim_fw_subset_subsumed:                 0
% 2.97/1.00  sim_bw_subset_subsumed:                 0
% 2.97/1.00  sim_fw_subsumed:                        0
% 2.97/1.00  sim_bw_subsumed:                        0
% 2.97/1.00  sim_fw_subsumption_res:                 0
% 2.97/1.00  sim_bw_subsumption_res:                 0
% 2.97/1.00  sim_tautology_del:                      0
% 2.97/1.00  sim_eq_tautology_del:                   0
% 2.97/1.00  sim_eq_res_simp:                        0
% 2.97/1.00  sim_fw_demodulated:                     0
% 2.97/1.00  sim_bw_demodulated:                     2
% 2.97/1.00  sim_light_normalised:                   0
% 2.97/1.00  sim_joinable_taut:                      0
% 2.97/1.00  sim_joinable_simp:                      0
% 2.97/1.00  sim_ac_normalised:                      0
% 2.97/1.00  sim_smt_subsumption:                    0
% 2.97/1.00  
%------------------------------------------------------------------------------
