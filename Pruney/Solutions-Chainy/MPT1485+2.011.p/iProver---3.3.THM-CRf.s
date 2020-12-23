%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:05 EST 2020

% Result     : Theorem 7.82s
% Output     : CNFRefutation 7.82s
% Verified   : 
% Statistics : Number of formulae       :  232 (1460 expanded)
%              Number of clauses        :  164 ( 380 expanded)
%              Number of leaves         :   19 ( 451 expanded)
%              Depth                    :   21
%              Number of atoms          : 1309 (9642 expanded)
%              Number of equality atoms :  281 (1554 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   21 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

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
    inference(nnf_transformation,[],[f23])).

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
    inference(flattening,[],[f37])).

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
    inference(rectify,[],[f38])).

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

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

fof(f44,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,sK4)) != X1
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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

fof(f42,plain,
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

fof(f45,plain,
    ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_orders_2(sK2)
    & v2_lattice3(sK2)
    & v1_lattice3(sK2)
    & v5_orders_2(sK2)
    & v3_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f31,f44,f43,f42])).

fof(f69,plain,(
    v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f68,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f70,plain,(
    v2_lattice3(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f63,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f72,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k13_lattice3(X0,X1,X2) = k13_lattice3(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k13_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k13_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(X0,X1,X2) = k13_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f9,axiom,(
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
             => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f67,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f45])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f5])).

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
    inference(flattening,[],[f20])).

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
    inference(nnf_transformation,[],[f21])).

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
    inference(flattening,[],[f32])).

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
    inference(rectify,[],[f33])).

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f50,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f73,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f45])).

fof(f51,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f55,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f74,plain,(
    k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_13,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK1(X0,X3,X2,X1),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_26,negated_conjecture,
    ( v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_568,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_26])).

cnf(c_569,plain,
    ( ~ l1_orders_2(sK2)
    | ~ v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_568])).

cnf(c_24,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_89,plain,
    ( ~ l1_orders_2(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_571,plain,
    ( ~ v2_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_569,c_26,c_24,c_89])).

cnf(c_816,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK1(X0,X2,X3,X1),X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X2,X3) = X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_571])).

cnf(c_817,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ v2_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k11_lattice3(sK2,X1,X2) = X0 ),
    inference(unflattening,[status(thm)],[c_816])).

cnf(c_27,negated_conjecture,
    ( v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_25,negated_conjecture,
    ( v2_lattice3(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_821,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | ~ r1_orders_2(sK2,X0,X1)
    | k11_lattice3(sK2,X1,X2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_817,c_27,c_25,c_24])).

cnf(c_822,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k11_lattice3(sK2,X1,X2) = X0 ),
    inference(renaming,[status(thm)],[c_821])).

cnf(c_1159,plain,
    ( ~ r1_orders_2(sK2,X0_46,X1_46)
    | ~ r1_orders_2(sK2,X0_46,X2_46)
    | r1_orders_2(sK2,sK1(sK2,X1_46,X2_46,X0_46),X1_46)
    | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X2_46,u1_struct_0(sK2))
    | k11_lattice3(sK2,X1_46,X2_46) = X0_46 ),
    inference(subtyping,[status(esa)],[c_822])).

cnf(c_19599,plain,
    ( ~ r1_orders_2(sK2,X0_46,k13_lattice3(sK2,sK3,sK4))
    | ~ r1_orders_2(sK2,X0_46,sK3)
    | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_46),sK3)
    | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46 ),
    inference(instantiation,[status(thm)],[c_1159])).

cnf(c_19616,plain,
    ( r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),sK3),sK3)
    | ~ r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
    | ~ r1_orders_2(sK2,sK3,sK3)
    | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3 ),
    inference(instantiation,[status(thm)],[c_19599])).

cnf(c_11,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK1(X0,X3,X2,X1),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_878,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK1(X0,X2,X3,X1),X1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X2,X3) = X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_571])).

cnf(c_879,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | ~ r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ v2_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k11_lattice3(sK2,X1,X2) = X0 ),
    inference(unflattening,[status(thm)],[c_878])).

cnf(c_883,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X0)
    | ~ r1_orders_2(sK2,X0,X2)
    | ~ r1_orders_2(sK2,X0,X1)
    | k11_lattice3(sK2,X1,X2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_879,c_27,c_25,c_24])).

cnf(c_884,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | ~ r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X0)
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k11_lattice3(sK2,X1,X2) = X0 ),
    inference(renaming,[status(thm)],[c_883])).

cnf(c_1157,plain,
    ( ~ r1_orders_2(sK2,X0_46,X1_46)
    | ~ r1_orders_2(sK2,X0_46,X2_46)
    | ~ r1_orders_2(sK2,sK1(sK2,X1_46,X2_46,X0_46),X0_46)
    | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X2_46,u1_struct_0(sK2))
    | k11_lattice3(sK2,X1_46,X2_46) = X0_46 ),
    inference(subtyping,[status(esa)],[c_884])).

cnf(c_19601,plain,
    ( ~ r1_orders_2(sK2,X0_46,k13_lattice3(sK2,sK3,sK4))
    | ~ r1_orders_2(sK2,X0_46,sK3)
    | ~ r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_46),X0_46)
    | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46 ),
    inference(instantiation,[status(thm)],[c_1157])).

cnf(c_19608,plain,
    ( ~ r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),sK3),sK3)
    | ~ r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
    | ~ r1_orders_2(sK2,sK3,sK3)
    | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3 ),
    inference(instantiation,[status(thm)],[c_19601])).

cnf(c_1180,plain,
    ( X0_46 != X1_46
    | X2_46 != X1_46
    | X2_46 = X0_46 ),
    theory(equality)).

cnf(c_3332,plain,
    ( X0_46 != X1_46
    | X0_46 = k11_lattice3(sK2,X2_46,X3_46)
    | k11_lattice3(sK2,X2_46,X3_46) != X1_46 ),
    inference(instantiation,[status(thm)],[c_1180])).

cnf(c_14815,plain,
    ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != X0_46
    | sK3 != X0_46
    | sK3 = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3332])).

cnf(c_14816,plain,
    ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3
    | sK3 = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_14815])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1175,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1556,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1175])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k12_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_982,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k12_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_24])).

cnf(c_983,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(k12_lattice3(sK2,X0,X1),u1_struct_0(sK2))
    | ~ v2_lattice3(sK2)
    | ~ v5_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_982])).

cnf(c_987,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(k12_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_983,c_27,c_25])).

cnf(c_1155,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | m1_subset_1(k12_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_987])).

cnf(c_1576,plain,
    ( m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k12_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1155])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_579,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_26])).

cnf(c_580,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k10_lattice3(sK2,X0,X1) = k13_lattice3(sK2,X0,X1) ),
    inference(unflattening,[status(thm)],[c_579])).

cnf(c_584,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k10_lattice3(sK2,X0,X1) = k13_lattice3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_580,c_27,c_24])).

cnf(c_1166,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | k10_lattice3(sK2,X0_46,X1_46) = k13_lattice3(sK2,X0_46,X1_46) ),
    inference(subtyping,[status(esa)],[c_584])).

cnf(c_1565,plain,
    ( k10_lattice3(sK2,X0_46,X1_46) = k13_lattice3(sK2,X0_46,X1_46)
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1166])).

cnf(c_2532,plain,
    ( k10_lattice3(sK2,sK3,X0_46) = k13_lattice3(sK2,sK3,X0_46)
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1556,c_1565])).

cnf(c_6614,plain,
    ( k10_lattice3(sK2,sK3,k12_lattice3(sK2,X0_46,X1_46)) = k13_lattice3(sK2,sK3,k12_lattice3(sK2,X0_46,X1_46))
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1576,c_2532])).

cnf(c_11245,plain,
    ( k10_lattice3(sK2,sK3,k12_lattice3(sK2,sK3,X0_46)) = k13_lattice3(sK2,sK3,k12_lattice3(sK2,sK3,X0_46))
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1556,c_6614])).

cnf(c_11621,plain,
    ( k10_lattice3(sK2,sK3,k12_lattice3(sK2,sK3,sK3)) = k13_lattice3(sK2,sK3,k12_lattice3(sK2,sK3,sK3)) ),
    inference(superposition,[status(thm)],[c_1556,c_11245])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | k13_lattice3(X1,X0,X2) = k13_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_621,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k13_lattice3(X1,X2,X0) = k13_lattice3(X1,X0,X2)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_26])).

cnf(c_622,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k13_lattice3(sK2,X0,X1) = k13_lattice3(sK2,X1,X0) ),
    inference(unflattening,[status(thm)],[c_621])).

cnf(c_626,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k13_lattice3(sK2,X0,X1) = k13_lattice3(sK2,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_622,c_27,c_24])).

cnf(c_1164,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | k13_lattice3(sK2,X0_46,X1_46) = k13_lattice3(sK2,X1_46,X0_46) ),
    inference(subtyping,[status(esa)],[c_626])).

cnf(c_1567,plain,
    ( k13_lattice3(sK2,X0_46,X1_46) = k13_lattice3(sK2,X1_46,X0_46)
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1164])).

cnf(c_3104,plain,
    ( k13_lattice3(sK2,X0_46,sK3) = k13_lattice3(sK2,sK3,X0_46)
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1556,c_1567])).

cnf(c_6611,plain,
    ( k13_lattice3(sK2,k12_lattice3(sK2,X0_46,X1_46),sK3) = k13_lattice3(sK2,sK3,k12_lattice3(sK2,X0_46,X1_46))
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1576,c_3104])).

cnf(c_10502,plain,
    ( k13_lattice3(sK2,sK3,k12_lattice3(sK2,sK3,X0_46)) = k13_lattice3(sK2,k12_lattice3(sK2,sK3,X0_46),sK3)
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1556,c_6611])).

cnf(c_10828,plain,
    ( k13_lattice3(sK2,sK3,k12_lattice3(sK2,sK3,sK3)) = k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK3),sK3) ),
    inference(superposition,[status(thm)],[c_1556,c_10502])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | k13_lattice3(X1,k12_lattice3(X1,X2,X0),X0) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_28,negated_conjecture,
    ( v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_338,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | k13_lattice3(X1,k12_lattice3(X1,X2,X0),X0) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_28])).

cnf(c_339,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v2_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | ~ v1_lattice3(sK2)
    | k13_lattice3(sK2,k12_lattice3(sK2,X0,X1),X1) = X1 ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_343,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k13_lattice3(sK2,k12_lattice3(sK2,X0,X1),X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_339,c_27,c_26,c_25,c_24])).

cnf(c_1174,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | k13_lattice3(sK2,k12_lattice3(sK2,X0_46,X1_46),X1_46) = X1_46 ),
    inference(subtyping,[status(esa)],[c_343])).

cnf(c_1557,plain,
    ( k13_lattice3(sK2,k12_lattice3(sK2,X0_46,X1_46),X1_46) = X1_46
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1174])).

cnf(c_1647,plain,
    ( k13_lattice3(sK2,k12_lattice3(sK2,sK3,X0_46),X0_46) = X0_46
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1556,c_1557])).

cnf(c_1900,plain,
    ( k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK3),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_1556,c_1647])).

cnf(c_10833,plain,
    ( k13_lattice3(sK2,sK3,k12_lattice3(sK2,sK3,sK3)) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_10828,c_1900])).

cnf(c_11626,plain,
    ( k10_lattice3(sK2,sK3,k12_lattice3(sK2,sK3,sK3)) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_11621,c_10833])).

cnf(c_10,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_165,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_0])).

cnf(c_166,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0) ),
    inference(renaming,[status(thm)],[c_165])).

cnf(c_548,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_166,c_26])).

cnf(c_549,plain,
    ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_548])).

cnf(c_551,plain,
    ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_549,c_27,c_24])).

cnf(c_552,plain,
    ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_551])).

cnf(c_1167,plain,
    ( r1_orders_2(sK2,X0_46,k10_lattice3(sK2,X0_46,X1_46))
    | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_552])).

cnf(c_1564,plain,
    ( r1_orders_2(sK2,X0_46,k10_lattice3(sK2,X0_46,X1_46)) = iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k10_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1167])).

cnf(c_1212,plain,
    ( r1_orders_2(sK2,X0_46,k10_lattice3(sK2,X0_46,X1_46)) = iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k10_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1167])).

cnf(c_1213,plain,
    ( k10_lattice3(sK2,X0_46,X1_46) = k13_lattice3(sK2,X0_46,X1_46)
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1166])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k13_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_600,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k13_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_26])).

cnf(c_601,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(k13_lattice3(sK2,X0,X1),u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_600])).

cnf(c_605,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(k13_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_601,c_27,c_24])).

cnf(c_1165,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | m1_subset_1(k13_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_605])).

cnf(c_1216,plain,
    ( m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k13_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1165])).

cnf(c_1182,plain,
    ( ~ m1_subset_1(X0_46,X0_47)
    | m1_subset_1(X1_46,X0_47)
    | X1_46 != X0_46 ),
    theory(equality)).

cnf(c_1622,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | m1_subset_1(k10_lattice3(sK2,X1_46,X2_46),u1_struct_0(sK2))
    | k10_lattice3(sK2,X1_46,X2_46) != X0_46 ),
    inference(instantiation,[status(thm)],[c_1182])).

cnf(c_1659,plain,
    ( m1_subset_1(k10_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2))
    | ~ m1_subset_1(k13_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2))
    | k10_lattice3(sK2,X0_46,X1_46) != k13_lattice3(sK2,X0_46,X1_46) ),
    inference(instantiation,[status(thm)],[c_1622])).

cnf(c_1660,plain,
    ( k10_lattice3(sK2,X0_46,X1_46) != k13_lattice3(sK2,X0_46,X1_46)
    | m1_subset_1(k10_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(k13_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1659])).

cnf(c_6992,plain,
    ( m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | r1_orders_2(sK2,X0_46,k10_lattice3(sK2,X0_46,X1_46)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1564,c_1212,c_1213,c_1216,c_1660])).

cnf(c_6993,plain,
    ( r1_orders_2(sK2,X0_46,k10_lattice3(sK2,X0_46,X1_46)) = iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6992])).

cnf(c_11795,plain,
    ( r1_orders_2(sK2,sK3,sK3) = iProver_top
    | m1_subset_1(k12_lattice3(sK2,sK3,sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11626,c_6993])).

cnf(c_1621,plain,
    ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != X0_46
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
    | sK3 != X0_46 ),
    inference(instantiation,[status(thm)],[c_1180])).

cnf(c_7602,plain,
    ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
    | sK3 != k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1621])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1176,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1555,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1176])).

cnf(c_3103,plain,
    ( k13_lattice3(sK2,X0_46,sK4) = k13_lattice3(sK2,sK4,X0_46)
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1555,c_1567])).

cnf(c_3155,plain,
    ( k13_lattice3(sK2,sK4,sK3) = k13_lattice3(sK2,sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1556,c_3103])).

cnf(c_2531,plain,
    ( k10_lattice3(sK2,sK4,X0_46) = k13_lattice3(sK2,sK4,X0_46)
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1555,c_1565])).

cnf(c_2817,plain,
    ( k10_lattice3(sK2,sK4,sK3) = k13_lattice3(sK2,sK4,sK3) ),
    inference(superposition,[status(thm)],[c_1556,c_2531])).

cnf(c_3224,plain,
    ( k10_lattice3(sK2,sK4,sK3) = k13_lattice3(sK2,sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_3155,c_2817])).

cnf(c_9,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_172,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_0])).

cnf(c_173,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0) ),
    inference(renaming,[status(thm)],[c_172])).

cnf(c_524,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_173,c_26])).

cnf(c_525,plain,
    ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X1,X0),u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_524])).

cnf(c_529,plain,
    ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X1,X0),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_525,c_27,c_24])).

cnf(c_530,plain,
    ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X1,X0),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_529])).

cnf(c_1168,plain,
    ( r1_orders_2(sK2,X0_46,k10_lattice3(sK2,X1_46,X0_46))
    | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X1_46,X0_46),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_530])).

cnf(c_1563,plain,
    ( r1_orders_2(sK2,X0_46,k10_lattice3(sK2,X1_46,X0_46)) = iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k10_lattice3(sK2,X1_46,X0_46),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1168])).

cnf(c_6971,plain,
    ( r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK4,sK3)) = iProver_top
    | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3224,c_1563])).

cnf(c_6982,plain,
    ( r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = iProver_top
    | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6971,c_3224])).

cnf(c_6989,plain,
    ( r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
    | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6982])).

cnf(c_6555,plain,
    ( m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1165])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_961,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_24])).

cnf(c_962,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v2_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | k11_lattice3(sK2,X0,X1) = k12_lattice3(sK2,X0,X1) ),
    inference(unflattening,[status(thm)],[c_961])).

cnf(c_966,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k11_lattice3(sK2,X0,X1) = k12_lattice3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_962,c_27,c_25])).

cnf(c_1156,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | k11_lattice3(sK2,X0_46,X1_46) = k12_lattice3(sK2,X0_46,X1_46) ),
    inference(subtyping,[status(esa)],[c_966])).

cnf(c_6053,plain,
    ( ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1156])).

cnf(c_1656,plain,
    ( X0_46 != X1_46
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != X1_46
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46 ),
    inference(instantiation,[status(thm)],[c_1180])).

cnf(c_1678,plain,
    ( X0_46 != k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1656])).

cnf(c_6052,plain,
    ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1678])).

cnf(c_5,plain,
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
    inference(cnf_transformation,[],[f55])).

cnf(c_198,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_5,c_0])).

cnf(c_199,plain,
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
    inference(renaming,[status(thm)],[c_198])).

cnf(c_396,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X1,sK0(X0,X3,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X3,X1) = X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_199,c_26])).

cnf(c_397,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X2,X1)
    | r1_orders_2(sK2,X2,sK0(sK2,X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k10_lattice3(sK2,X0,X2) = X1 ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_401,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X2,X1)
    | r1_orders_2(sK2,X2,sK0(sK2,X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k10_lattice3(sK2,X0,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_397,c_27,c_24])).

cnf(c_402,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X2,X1)
    | r1_orders_2(sK2,X2,sK0(sK2,X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k10_lattice3(sK2,X0,X2) = X1 ),
    inference(renaming,[status(thm)],[c_401])).

cnf(c_1172,plain,
    ( ~ r1_orders_2(sK2,X0_46,X1_46)
    | ~ r1_orders_2(sK2,X2_46,X1_46)
    | r1_orders_2(sK2,X2_46,sK0(sK2,X0_46,X2_46,X1_46))
    | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X2_46,u1_struct_0(sK2))
    | k10_lattice3(sK2,X0_46,X2_46) = X1_46 ),
    inference(subtyping,[status(esa)],[c_402])).

cnf(c_1559,plain,
    ( k10_lattice3(sK2,X0_46,X1_46) = X2_46
    | r1_orders_2(sK2,X0_46,X2_46) != iProver_top
    | r1_orders_2(sK2,X1_46,X2_46) != iProver_top
    | r1_orders_2(sK2,X1_46,sK0(sK2,X0_46,X1_46,X2_46)) = iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1172])).

cnf(c_4,plain,
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
    inference(cnf_transformation,[],[f56])).

cnf(c_203,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_4,c_0])).

cnf(c_204,plain,
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
    inference(renaming,[status(thm)],[c_203])).

cnf(c_363,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X3,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X3,X1) = X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_204,c_26])).

cnf(c_364,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X2,X1)
    | ~ r1_orders_2(sK2,X1,sK0(sK2,X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k10_lattice3(sK2,X0,X2) = X1 ),
    inference(unflattening,[status(thm)],[c_363])).

cnf(c_368,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X2,X1)
    | ~ r1_orders_2(sK2,X1,sK0(sK2,X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k10_lattice3(sK2,X0,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_364,c_27,c_24])).

cnf(c_369,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X2,X1)
    | ~ r1_orders_2(sK2,X1,sK0(sK2,X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k10_lattice3(sK2,X0,X2) = X1 ),
    inference(renaming,[status(thm)],[c_368])).

cnf(c_1173,plain,
    ( ~ r1_orders_2(sK2,X0_46,X1_46)
    | ~ r1_orders_2(sK2,X2_46,X1_46)
    | ~ r1_orders_2(sK2,X1_46,sK0(sK2,X0_46,X2_46,X1_46))
    | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X2_46,u1_struct_0(sK2))
    | k10_lattice3(sK2,X0_46,X2_46) = X1_46 ),
    inference(subtyping,[status(esa)],[c_369])).

cnf(c_1558,plain,
    ( k10_lattice3(sK2,X0_46,X1_46) = X2_46
    | r1_orders_2(sK2,X0_46,X2_46) != iProver_top
    | r1_orders_2(sK2,X1_46,X2_46) != iProver_top
    | r1_orders_2(sK2,X2_46,sK0(sK2,X0_46,X1_46,X2_46)) != iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1173])).

cnf(c_3161,plain,
    ( k10_lattice3(sK2,X0_46,X1_46) = X1_46
    | r1_orders_2(sK2,X0_46,X1_46) != iProver_top
    | r1_orders_2(sK2,X1_46,X1_46) != iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1559,c_1558])).

cnf(c_3163,plain,
    ( k10_lattice3(sK2,sK3,sK3) = sK3
    | r1_orders_2(sK2,sK3,sK3) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3161])).

cnf(c_1179,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_2938,plain,
    ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1179])).

cnf(c_1879,plain,
    ( X0_46 != X1_46
    | X0_46 = k10_lattice3(sK2,X2_46,X3_46)
    | k10_lattice3(sK2,X2_46,X3_46) != X1_46 ),
    inference(instantiation,[status(thm)],[c_1180])).

cnf(c_1880,plain,
    ( k10_lattice3(sK2,sK3,sK3) != sK3
    | sK3 = k10_lattice3(sK2,sK3,sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1879])).

cnf(c_1184,plain,
    ( ~ r1_orders_2(X0_48,X0_46,X1_46)
    | r1_orders_2(X0_48,X2_46,X3_46)
    | X2_46 != X0_46
    | X3_46 != X1_46 ),
    theory(equality)).

cnf(c_1629,plain,
    ( ~ r1_orders_2(sK2,X0_46,X1_46)
    | r1_orders_2(sK2,X2_46,X3_46)
    | X2_46 != X0_46
    | X3_46 != X1_46 ),
    inference(instantiation,[status(thm)],[c_1184])).

cnf(c_1683,plain,
    ( r1_orders_2(sK2,X0_46,X1_46)
    | ~ r1_orders_2(sK2,X2_46,k10_lattice3(sK2,X2_46,X3_46))
    | X0_46 != X2_46
    | X1_46 != k10_lattice3(sK2,X2_46,X3_46) ),
    inference(instantiation,[status(thm)],[c_1629])).

cnf(c_1733,plain,
    ( ~ r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK3))
    | r1_orders_2(sK2,sK3,sK3)
    | sK3 != k10_lattice3(sK2,sK3,sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1683])).

cnf(c_1661,plain,
    ( m1_subset_1(k10_lattice3(sK2,sK3,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK3),u1_struct_0(sK2))
    | k10_lattice3(sK2,sK3,sK3) != k13_lattice3(sK2,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_1659])).

cnf(c_1242,plain,
    ( m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k12_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1155])).

cnf(c_1244,plain,
    ( m1_subset_1(k12_lattice3(sK2,sK3,sK3),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1242])).

cnf(c_1217,plain,
    ( m1_subset_1(k13_lattice3(sK2,sK3,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1165])).

cnf(c_1214,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k10_lattice3(sK2,sK3,sK3) = k13_lattice3(sK2,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_1166])).

cnf(c_1210,plain,
    ( r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK3))
    | ~ m1_subset_1(k10_lattice3(sK2,sK3,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1168])).

cnf(c_21,negated_conjecture,
    ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1177,negated_conjecture,
    ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1190,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1179])).

cnf(c_34,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19616,c_19608,c_14816,c_11795,c_7602,c_6989,c_6555,c_6053,c_6052,c_3163,c_2938,c_1880,c_1733,c_1661,c_1244,c_1217,c_1214,c_1210,c_1177,c_1190,c_22,c_34,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:13:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.82/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.82/1.48  
% 7.82/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.82/1.48  
% 7.82/1.48  ------  iProver source info
% 7.82/1.48  
% 7.82/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.82/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.82/1.48  git: non_committed_changes: false
% 7.82/1.48  git: last_make_outside_of_git: false
% 7.82/1.48  
% 7.82/1.48  ------ 
% 7.82/1.48  
% 7.82/1.48  ------ Input Options
% 7.82/1.48  
% 7.82/1.48  --out_options                           all
% 7.82/1.48  --tptp_safe_out                         true
% 7.82/1.48  --problem_path                          ""
% 7.82/1.48  --include_path                          ""
% 7.82/1.48  --clausifier                            res/vclausify_rel
% 7.82/1.48  --clausifier_options                    ""
% 7.82/1.48  --stdin                                 false
% 7.82/1.48  --stats_out                             all
% 7.82/1.48  
% 7.82/1.48  ------ General Options
% 7.82/1.48  
% 7.82/1.48  --fof                                   false
% 7.82/1.48  --time_out_real                         305.
% 7.82/1.48  --time_out_virtual                      -1.
% 7.82/1.48  --symbol_type_check                     false
% 7.82/1.48  --clausify_out                          false
% 7.82/1.48  --sig_cnt_out                           false
% 7.82/1.48  --trig_cnt_out                          false
% 7.82/1.48  --trig_cnt_out_tolerance                1.
% 7.82/1.48  --trig_cnt_out_sk_spl                   false
% 7.82/1.48  --abstr_cl_out                          false
% 7.82/1.48  
% 7.82/1.48  ------ Global Options
% 7.82/1.48  
% 7.82/1.48  --schedule                              default
% 7.82/1.48  --add_important_lit                     false
% 7.82/1.48  --prop_solver_per_cl                    1000
% 7.82/1.48  --min_unsat_core                        false
% 7.82/1.48  --soft_assumptions                      false
% 7.82/1.48  --soft_lemma_size                       3
% 7.82/1.48  --prop_impl_unit_size                   0
% 7.82/1.48  --prop_impl_unit                        []
% 7.82/1.48  --share_sel_clauses                     true
% 7.82/1.48  --reset_solvers                         false
% 7.82/1.48  --bc_imp_inh                            [conj_cone]
% 7.82/1.48  --conj_cone_tolerance                   3.
% 7.82/1.48  --extra_neg_conj                        none
% 7.82/1.48  --large_theory_mode                     true
% 7.82/1.48  --prolific_symb_bound                   200
% 7.82/1.48  --lt_threshold                          2000
% 7.82/1.48  --clause_weak_htbl                      true
% 7.82/1.48  --gc_record_bc_elim                     false
% 7.82/1.48  
% 7.82/1.48  ------ Preprocessing Options
% 7.82/1.48  
% 7.82/1.48  --preprocessing_flag                    true
% 7.82/1.48  --time_out_prep_mult                    0.1
% 7.82/1.48  --splitting_mode                        input
% 7.82/1.48  --splitting_grd                         true
% 7.82/1.48  --splitting_cvd                         false
% 7.82/1.48  --splitting_cvd_svl                     false
% 7.82/1.48  --splitting_nvd                         32
% 7.82/1.48  --sub_typing                            true
% 7.82/1.48  --prep_gs_sim                           true
% 7.82/1.48  --prep_unflatten                        true
% 7.82/1.48  --prep_res_sim                          true
% 7.82/1.48  --prep_upred                            true
% 7.82/1.48  --prep_sem_filter                       exhaustive
% 7.82/1.48  --prep_sem_filter_out                   false
% 7.82/1.48  --pred_elim                             true
% 7.82/1.48  --res_sim_input                         true
% 7.82/1.48  --eq_ax_congr_red                       true
% 7.82/1.48  --pure_diseq_elim                       true
% 7.82/1.48  --brand_transform                       false
% 7.82/1.48  --non_eq_to_eq                          false
% 7.82/1.48  --prep_def_merge                        true
% 7.82/1.48  --prep_def_merge_prop_impl              false
% 7.82/1.48  --prep_def_merge_mbd                    true
% 7.82/1.48  --prep_def_merge_tr_red                 false
% 7.82/1.48  --prep_def_merge_tr_cl                  false
% 7.82/1.48  --smt_preprocessing                     true
% 7.82/1.48  --smt_ac_axioms                         fast
% 7.82/1.48  --preprocessed_out                      false
% 7.82/1.48  --preprocessed_stats                    false
% 7.82/1.48  
% 7.82/1.48  ------ Abstraction refinement Options
% 7.82/1.48  
% 7.82/1.48  --abstr_ref                             []
% 7.82/1.48  --abstr_ref_prep                        false
% 7.82/1.48  --abstr_ref_until_sat                   false
% 7.82/1.48  --abstr_ref_sig_restrict                funpre
% 7.82/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.82/1.48  --abstr_ref_under                       []
% 7.82/1.48  
% 7.82/1.48  ------ SAT Options
% 7.82/1.48  
% 7.82/1.48  --sat_mode                              false
% 7.82/1.48  --sat_fm_restart_options                ""
% 7.82/1.48  --sat_gr_def                            false
% 7.82/1.48  --sat_epr_types                         true
% 7.82/1.48  --sat_non_cyclic_types                  false
% 7.82/1.48  --sat_finite_models                     false
% 7.82/1.48  --sat_fm_lemmas                         false
% 7.82/1.48  --sat_fm_prep                           false
% 7.82/1.48  --sat_fm_uc_incr                        true
% 7.82/1.48  --sat_out_model                         small
% 7.82/1.48  --sat_out_clauses                       false
% 7.82/1.48  
% 7.82/1.48  ------ QBF Options
% 7.82/1.48  
% 7.82/1.48  --qbf_mode                              false
% 7.82/1.48  --qbf_elim_univ                         false
% 7.82/1.48  --qbf_dom_inst                          none
% 7.82/1.48  --qbf_dom_pre_inst                      false
% 7.82/1.48  --qbf_sk_in                             false
% 7.82/1.48  --qbf_pred_elim                         true
% 7.82/1.48  --qbf_split                             512
% 7.82/1.48  
% 7.82/1.48  ------ BMC1 Options
% 7.82/1.48  
% 7.82/1.48  --bmc1_incremental                      false
% 7.82/1.48  --bmc1_axioms                           reachable_all
% 7.82/1.48  --bmc1_min_bound                        0
% 7.82/1.48  --bmc1_max_bound                        -1
% 7.82/1.48  --bmc1_max_bound_default                -1
% 7.82/1.48  --bmc1_symbol_reachability              true
% 7.82/1.48  --bmc1_property_lemmas                  false
% 7.82/1.48  --bmc1_k_induction                      false
% 7.82/1.48  --bmc1_non_equiv_states                 false
% 7.82/1.48  --bmc1_deadlock                         false
% 7.82/1.48  --bmc1_ucm                              false
% 7.82/1.48  --bmc1_add_unsat_core                   none
% 7.82/1.48  --bmc1_unsat_core_children              false
% 7.82/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.82/1.48  --bmc1_out_stat                         full
% 7.82/1.48  --bmc1_ground_init                      false
% 7.82/1.48  --bmc1_pre_inst_next_state              false
% 7.82/1.48  --bmc1_pre_inst_state                   false
% 7.82/1.48  --bmc1_pre_inst_reach_state             false
% 7.82/1.48  --bmc1_out_unsat_core                   false
% 7.82/1.48  --bmc1_aig_witness_out                  false
% 7.82/1.48  --bmc1_verbose                          false
% 7.82/1.48  --bmc1_dump_clauses_tptp                false
% 7.82/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.82/1.48  --bmc1_dump_file                        -
% 7.82/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.82/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.82/1.48  --bmc1_ucm_extend_mode                  1
% 7.82/1.48  --bmc1_ucm_init_mode                    2
% 7.82/1.48  --bmc1_ucm_cone_mode                    none
% 7.82/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.82/1.48  --bmc1_ucm_relax_model                  4
% 7.82/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.82/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.82/1.48  --bmc1_ucm_layered_model                none
% 7.82/1.48  --bmc1_ucm_max_lemma_size               10
% 7.82/1.48  
% 7.82/1.48  ------ AIG Options
% 7.82/1.48  
% 7.82/1.48  --aig_mode                              false
% 7.82/1.48  
% 7.82/1.48  ------ Instantiation Options
% 7.82/1.48  
% 7.82/1.48  --instantiation_flag                    true
% 7.82/1.48  --inst_sos_flag                         true
% 7.82/1.48  --inst_sos_phase                        true
% 7.82/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.82/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.82/1.48  --inst_lit_sel_side                     num_symb
% 7.82/1.48  --inst_solver_per_active                1400
% 7.82/1.48  --inst_solver_calls_frac                1.
% 7.82/1.48  --inst_passive_queue_type               priority_queues
% 7.82/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.82/1.48  --inst_passive_queues_freq              [25;2]
% 7.82/1.48  --inst_dismatching                      true
% 7.82/1.48  --inst_eager_unprocessed_to_passive     true
% 7.82/1.48  --inst_prop_sim_given                   true
% 7.82/1.48  --inst_prop_sim_new                     false
% 7.82/1.48  --inst_subs_new                         false
% 7.82/1.48  --inst_eq_res_simp                      false
% 7.82/1.48  --inst_subs_given                       false
% 7.82/1.48  --inst_orphan_elimination               true
% 7.82/1.48  --inst_learning_loop_flag               true
% 7.82/1.48  --inst_learning_start                   3000
% 7.82/1.48  --inst_learning_factor                  2
% 7.82/1.48  --inst_start_prop_sim_after_learn       3
% 7.82/1.48  --inst_sel_renew                        solver
% 7.82/1.48  --inst_lit_activity_flag                true
% 7.82/1.48  --inst_restr_to_given                   false
% 7.82/1.48  --inst_activity_threshold               500
% 7.82/1.48  --inst_out_proof                        true
% 7.82/1.48  
% 7.82/1.48  ------ Resolution Options
% 7.82/1.48  
% 7.82/1.48  --resolution_flag                       true
% 7.82/1.48  --res_lit_sel                           adaptive
% 7.82/1.48  --res_lit_sel_side                      none
% 7.82/1.48  --res_ordering                          kbo
% 7.82/1.48  --res_to_prop_solver                    active
% 7.82/1.48  --res_prop_simpl_new                    false
% 7.82/1.48  --res_prop_simpl_given                  true
% 7.82/1.48  --res_passive_queue_type                priority_queues
% 7.82/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.82/1.48  --res_passive_queues_freq               [15;5]
% 7.82/1.48  --res_forward_subs                      full
% 7.82/1.48  --res_backward_subs                     full
% 7.82/1.48  --res_forward_subs_resolution           true
% 7.82/1.48  --res_backward_subs_resolution          true
% 7.82/1.48  --res_orphan_elimination                true
% 7.82/1.48  --res_time_limit                        2.
% 7.82/1.48  --res_out_proof                         true
% 7.82/1.48  
% 7.82/1.48  ------ Superposition Options
% 7.82/1.48  
% 7.82/1.48  --superposition_flag                    true
% 7.82/1.48  --sup_passive_queue_type                priority_queues
% 7.82/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.82/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.82/1.48  --demod_completeness_check              fast
% 7.82/1.48  --demod_use_ground                      true
% 7.82/1.48  --sup_to_prop_solver                    passive
% 7.82/1.48  --sup_prop_simpl_new                    true
% 7.82/1.48  --sup_prop_simpl_given                  true
% 7.82/1.48  --sup_fun_splitting                     true
% 7.82/1.48  --sup_smt_interval                      50000
% 7.82/1.48  
% 7.82/1.48  ------ Superposition Simplification Setup
% 7.82/1.48  
% 7.82/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.82/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.82/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.82/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.82/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.82/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.82/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.82/1.48  --sup_immed_triv                        [TrivRules]
% 7.82/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.82/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.82/1.48  --sup_immed_bw_main                     []
% 7.82/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.82/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.82/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.82/1.48  --sup_input_bw                          []
% 7.82/1.48  
% 7.82/1.48  ------ Combination Options
% 7.82/1.48  
% 7.82/1.48  --comb_res_mult                         3
% 7.82/1.48  --comb_sup_mult                         2
% 7.82/1.48  --comb_inst_mult                        10
% 7.82/1.48  
% 7.82/1.48  ------ Debug Options
% 7.82/1.48  
% 7.82/1.48  --dbg_backtrace                         false
% 7.82/1.48  --dbg_dump_prop_clauses                 false
% 7.82/1.48  --dbg_dump_prop_clauses_file            -
% 7.82/1.48  --dbg_out_stat                          false
% 7.82/1.48  ------ Parsing...
% 7.82/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.82/1.48  
% 7.82/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 7.82/1.48  
% 7.82/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.82/1.48  
% 7.82/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.82/1.48  ------ Proving...
% 7.82/1.48  ------ Problem Properties 
% 7.82/1.48  
% 7.82/1.48  
% 7.82/1.48  clauses                                 23
% 7.82/1.48  conjectures                             3
% 7.82/1.48  EPR                                     0
% 7.82/1.48  Horn                                    17
% 7.82/1.48  unary                                   3
% 7.82/1.48  binary                                  0
% 7.82/1.48  lits                                    107
% 7.82/1.48  lits eq                                 13
% 7.82/1.48  fd_pure                                 0
% 7.82/1.48  fd_pseudo                               0
% 7.82/1.48  fd_cond                                 0
% 7.82/1.48  fd_pseudo_cond                          8
% 7.82/1.48  AC symbols                              0
% 7.82/1.48  
% 7.82/1.48  ------ Schedule dynamic 5 is on 
% 7.82/1.48  
% 7.82/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.82/1.48  
% 7.82/1.48  
% 7.82/1.48  ------ 
% 7.82/1.48  Current options:
% 7.82/1.48  ------ 
% 7.82/1.48  
% 7.82/1.48  ------ Input Options
% 7.82/1.48  
% 7.82/1.48  --out_options                           all
% 7.82/1.48  --tptp_safe_out                         true
% 7.82/1.48  --problem_path                          ""
% 7.82/1.48  --include_path                          ""
% 7.82/1.48  --clausifier                            res/vclausify_rel
% 7.82/1.48  --clausifier_options                    ""
% 7.82/1.48  --stdin                                 false
% 7.82/1.48  --stats_out                             all
% 7.82/1.48  
% 7.82/1.48  ------ General Options
% 7.82/1.48  
% 7.82/1.48  --fof                                   false
% 7.82/1.48  --time_out_real                         305.
% 7.82/1.48  --time_out_virtual                      -1.
% 7.82/1.48  --symbol_type_check                     false
% 7.82/1.48  --clausify_out                          false
% 7.82/1.48  --sig_cnt_out                           false
% 7.82/1.48  --trig_cnt_out                          false
% 7.82/1.48  --trig_cnt_out_tolerance                1.
% 7.82/1.48  --trig_cnt_out_sk_spl                   false
% 7.82/1.48  --abstr_cl_out                          false
% 7.82/1.48  
% 7.82/1.48  ------ Global Options
% 7.82/1.48  
% 7.82/1.48  --schedule                              default
% 7.82/1.48  --add_important_lit                     false
% 7.82/1.48  --prop_solver_per_cl                    1000
% 7.82/1.48  --min_unsat_core                        false
% 7.82/1.48  --soft_assumptions                      false
% 7.82/1.48  --soft_lemma_size                       3
% 7.82/1.48  --prop_impl_unit_size                   0
% 7.82/1.48  --prop_impl_unit                        []
% 7.82/1.48  --share_sel_clauses                     true
% 7.82/1.48  --reset_solvers                         false
% 7.82/1.48  --bc_imp_inh                            [conj_cone]
% 7.82/1.48  --conj_cone_tolerance                   3.
% 7.82/1.48  --extra_neg_conj                        none
% 7.82/1.48  --large_theory_mode                     true
% 7.82/1.48  --prolific_symb_bound                   200
% 7.82/1.48  --lt_threshold                          2000
% 7.82/1.48  --clause_weak_htbl                      true
% 7.82/1.48  --gc_record_bc_elim                     false
% 7.82/1.48  
% 7.82/1.48  ------ Preprocessing Options
% 7.82/1.48  
% 7.82/1.48  --preprocessing_flag                    true
% 7.82/1.48  --time_out_prep_mult                    0.1
% 7.82/1.48  --splitting_mode                        input
% 7.82/1.48  --splitting_grd                         true
% 7.82/1.48  --splitting_cvd                         false
% 7.82/1.48  --splitting_cvd_svl                     false
% 7.82/1.48  --splitting_nvd                         32
% 7.82/1.48  --sub_typing                            true
% 7.82/1.48  --prep_gs_sim                           true
% 7.82/1.48  --prep_unflatten                        true
% 7.82/1.48  --prep_res_sim                          true
% 7.82/1.48  --prep_upred                            true
% 7.82/1.48  --prep_sem_filter                       exhaustive
% 7.82/1.48  --prep_sem_filter_out                   false
% 7.82/1.48  --pred_elim                             true
% 7.82/1.48  --res_sim_input                         true
% 7.82/1.48  --eq_ax_congr_red                       true
% 7.82/1.48  --pure_diseq_elim                       true
% 7.82/1.48  --brand_transform                       false
% 7.82/1.48  --non_eq_to_eq                          false
% 7.82/1.48  --prep_def_merge                        true
% 7.82/1.48  --prep_def_merge_prop_impl              false
% 7.82/1.48  --prep_def_merge_mbd                    true
% 7.82/1.48  --prep_def_merge_tr_red                 false
% 7.82/1.48  --prep_def_merge_tr_cl                  false
% 7.82/1.48  --smt_preprocessing                     true
% 7.82/1.48  --smt_ac_axioms                         fast
% 7.82/1.48  --preprocessed_out                      false
% 7.82/1.48  --preprocessed_stats                    false
% 7.82/1.48  
% 7.82/1.48  ------ Abstraction refinement Options
% 7.82/1.48  
% 7.82/1.48  --abstr_ref                             []
% 7.82/1.48  --abstr_ref_prep                        false
% 7.82/1.48  --abstr_ref_until_sat                   false
% 7.82/1.48  --abstr_ref_sig_restrict                funpre
% 7.82/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.82/1.48  --abstr_ref_under                       []
% 7.82/1.48  
% 7.82/1.48  ------ SAT Options
% 7.82/1.48  
% 7.82/1.48  --sat_mode                              false
% 7.82/1.48  --sat_fm_restart_options                ""
% 7.82/1.48  --sat_gr_def                            false
% 7.82/1.48  --sat_epr_types                         true
% 7.82/1.48  --sat_non_cyclic_types                  false
% 7.82/1.48  --sat_finite_models                     false
% 7.82/1.48  --sat_fm_lemmas                         false
% 7.82/1.48  --sat_fm_prep                           false
% 7.82/1.48  --sat_fm_uc_incr                        true
% 7.82/1.48  --sat_out_model                         small
% 7.82/1.48  --sat_out_clauses                       false
% 7.82/1.48  
% 7.82/1.48  ------ QBF Options
% 7.82/1.48  
% 7.82/1.48  --qbf_mode                              false
% 7.82/1.48  --qbf_elim_univ                         false
% 7.82/1.48  --qbf_dom_inst                          none
% 7.82/1.48  --qbf_dom_pre_inst                      false
% 7.82/1.48  --qbf_sk_in                             false
% 7.82/1.48  --qbf_pred_elim                         true
% 7.82/1.48  --qbf_split                             512
% 7.82/1.48  
% 7.82/1.48  ------ BMC1 Options
% 7.82/1.48  
% 7.82/1.48  --bmc1_incremental                      false
% 7.82/1.48  --bmc1_axioms                           reachable_all
% 7.82/1.48  --bmc1_min_bound                        0
% 7.82/1.48  --bmc1_max_bound                        -1
% 7.82/1.48  --bmc1_max_bound_default                -1
% 7.82/1.48  --bmc1_symbol_reachability              true
% 7.82/1.48  --bmc1_property_lemmas                  false
% 7.82/1.48  --bmc1_k_induction                      false
% 7.82/1.48  --bmc1_non_equiv_states                 false
% 7.82/1.48  --bmc1_deadlock                         false
% 7.82/1.48  --bmc1_ucm                              false
% 7.82/1.48  --bmc1_add_unsat_core                   none
% 7.82/1.48  --bmc1_unsat_core_children              false
% 7.82/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.82/1.48  --bmc1_out_stat                         full
% 7.82/1.48  --bmc1_ground_init                      false
% 7.82/1.48  --bmc1_pre_inst_next_state              false
% 7.82/1.48  --bmc1_pre_inst_state                   false
% 7.82/1.48  --bmc1_pre_inst_reach_state             false
% 7.82/1.48  --bmc1_out_unsat_core                   false
% 7.82/1.48  --bmc1_aig_witness_out                  false
% 7.82/1.48  --bmc1_verbose                          false
% 7.82/1.48  --bmc1_dump_clauses_tptp                false
% 7.82/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.82/1.48  --bmc1_dump_file                        -
% 7.82/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.82/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.82/1.48  --bmc1_ucm_extend_mode                  1
% 7.82/1.48  --bmc1_ucm_init_mode                    2
% 7.82/1.48  --bmc1_ucm_cone_mode                    none
% 7.82/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.82/1.48  --bmc1_ucm_relax_model                  4
% 7.82/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.82/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.82/1.48  --bmc1_ucm_layered_model                none
% 7.82/1.48  --bmc1_ucm_max_lemma_size               10
% 7.82/1.48  
% 7.82/1.48  ------ AIG Options
% 7.82/1.48  
% 7.82/1.48  --aig_mode                              false
% 7.82/1.48  
% 7.82/1.48  ------ Instantiation Options
% 7.82/1.48  
% 7.82/1.48  --instantiation_flag                    true
% 7.82/1.48  --inst_sos_flag                         true
% 7.82/1.48  --inst_sos_phase                        true
% 7.82/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.82/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.82/1.48  --inst_lit_sel_side                     none
% 7.82/1.48  --inst_solver_per_active                1400
% 7.82/1.48  --inst_solver_calls_frac                1.
% 7.82/1.48  --inst_passive_queue_type               priority_queues
% 7.82/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.82/1.48  --inst_passive_queues_freq              [25;2]
% 7.82/1.48  --inst_dismatching                      true
% 7.82/1.48  --inst_eager_unprocessed_to_passive     true
% 7.82/1.48  --inst_prop_sim_given                   true
% 7.82/1.48  --inst_prop_sim_new                     false
% 7.82/1.48  --inst_subs_new                         false
% 7.82/1.48  --inst_eq_res_simp                      false
% 7.82/1.48  --inst_subs_given                       false
% 7.82/1.48  --inst_orphan_elimination               true
% 7.82/1.48  --inst_learning_loop_flag               true
% 7.82/1.48  --inst_learning_start                   3000
% 7.82/1.48  --inst_learning_factor                  2
% 7.82/1.48  --inst_start_prop_sim_after_learn       3
% 7.82/1.48  --inst_sel_renew                        solver
% 7.82/1.48  --inst_lit_activity_flag                true
% 7.82/1.48  --inst_restr_to_given                   false
% 7.82/1.48  --inst_activity_threshold               500
% 7.82/1.48  --inst_out_proof                        true
% 7.82/1.48  
% 7.82/1.48  ------ Resolution Options
% 7.82/1.48  
% 7.82/1.48  --resolution_flag                       false
% 7.82/1.48  --res_lit_sel                           adaptive
% 7.82/1.48  --res_lit_sel_side                      none
% 7.82/1.48  --res_ordering                          kbo
% 7.82/1.48  --res_to_prop_solver                    active
% 7.82/1.48  --res_prop_simpl_new                    false
% 7.82/1.48  --res_prop_simpl_given                  true
% 7.82/1.48  --res_passive_queue_type                priority_queues
% 7.82/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.82/1.48  --res_passive_queues_freq               [15;5]
% 7.82/1.48  --res_forward_subs                      full
% 7.82/1.48  --res_backward_subs                     full
% 7.82/1.48  --res_forward_subs_resolution           true
% 7.82/1.48  --res_backward_subs_resolution          true
% 7.82/1.48  --res_orphan_elimination                true
% 7.82/1.48  --res_time_limit                        2.
% 7.82/1.48  --res_out_proof                         true
% 7.82/1.48  
% 7.82/1.48  ------ Superposition Options
% 7.82/1.48  
% 7.82/1.48  --superposition_flag                    true
% 7.82/1.48  --sup_passive_queue_type                priority_queues
% 7.82/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.82/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.82/1.48  --demod_completeness_check              fast
% 7.82/1.48  --demod_use_ground                      true
% 7.82/1.48  --sup_to_prop_solver                    passive
% 7.82/1.48  --sup_prop_simpl_new                    true
% 7.82/1.48  --sup_prop_simpl_given                  true
% 7.82/1.48  --sup_fun_splitting                     true
% 7.82/1.48  --sup_smt_interval                      50000
% 7.82/1.48  
% 7.82/1.48  ------ Superposition Simplification Setup
% 7.82/1.48  
% 7.82/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.82/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.82/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.82/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.82/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.82/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.82/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.82/1.48  --sup_immed_triv                        [TrivRules]
% 7.82/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.82/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.82/1.48  --sup_immed_bw_main                     []
% 7.82/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.82/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.82/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.82/1.48  --sup_input_bw                          []
% 7.82/1.48  
% 7.82/1.48  ------ Combination Options
% 7.82/1.48  
% 7.82/1.48  --comb_res_mult                         3
% 7.82/1.48  --comb_sup_mult                         2
% 7.82/1.48  --comb_inst_mult                        10
% 7.82/1.48  
% 7.82/1.48  ------ Debug Options
% 7.82/1.48  
% 7.82/1.48  --dbg_backtrace                         false
% 7.82/1.48  --dbg_dump_prop_clauses                 false
% 7.82/1.48  --dbg_dump_prop_clauses_file            -
% 7.82/1.48  --dbg_out_stat                          false
% 7.82/1.48  
% 7.82/1.48  
% 7.82/1.48  
% 7.82/1.48  
% 7.82/1.48  ------ Proving...
% 7.82/1.48  
% 7.82/1.48  
% 7.82/1.48  % SZS status Theorem for theBenchmark.p
% 7.82/1.48  
% 7.82/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.82/1.48  
% 7.82/1.48  fof(f6,axiom,(
% 7.82/1.48    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 7.82/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.82/1.48  
% 7.82/1.48  fof(f22,plain,(
% 7.82/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 7.82/1.48    inference(ennf_transformation,[],[f6])).
% 7.82/1.48  
% 7.82/1.48  fof(f23,plain,(
% 7.82/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 7.82/1.48    inference(flattening,[],[f22])).
% 7.82/1.48  
% 7.82/1.48  fof(f37,plain,(
% 7.82/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 7.82/1.48    inference(nnf_transformation,[],[f23])).
% 7.82/1.48  
% 7.82/1.48  fof(f38,plain,(
% 7.82/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 7.82/1.48    inference(flattening,[],[f37])).
% 7.82/1.48  
% 7.82/1.48  fof(f39,plain,(
% 7.82/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 7.82/1.48    inference(rectify,[],[f38])).
% 7.82/1.48  
% 7.82/1.48  fof(f40,plain,(
% 7.82/1.48    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK1(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X1) & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0))))),
% 7.82/1.48    introduced(choice_axiom,[])).
% 7.82/1.48  
% 7.82/1.48  fof(f41,plain,(
% 7.82/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,sK1(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X1) & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 7.82/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).
% 7.82/1.48  
% 7.82/1.48  fof(f61,plain,(
% 7.82/1.48    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | r1_orders_2(X0,sK1(X0,X1,X2,X3),X1) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 7.82/1.48    inference(cnf_transformation,[],[f41])).
% 7.82/1.48  
% 7.82/1.48  fof(f1,axiom,(
% 7.82/1.48    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 7.82/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.82/1.48  
% 7.82/1.48  fof(f12,plain,(
% 7.82/1.48    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 7.82/1.48    inference(ennf_transformation,[],[f1])).
% 7.82/1.48  
% 7.82/1.48  fof(f13,plain,(
% 7.82/1.48    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 7.82/1.48    inference(flattening,[],[f12])).
% 7.82/1.48  
% 7.82/1.48  fof(f46,plain,(
% 7.82/1.48    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 7.82/1.48    inference(cnf_transformation,[],[f13])).
% 7.82/1.48  
% 7.82/1.48  fof(f10,conjecture,(
% 7.82/1.48    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1)))),
% 7.82/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.82/1.48  
% 7.82/1.48  fof(f11,negated_conjecture,(
% 7.82/1.48    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1)))),
% 7.82/1.48    inference(negated_conjecture,[],[f10])).
% 7.82/1.48  
% 7.82/1.48  fof(f30,plain,(
% 7.82/1.48    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)))),
% 7.82/1.48    inference(ennf_transformation,[],[f11])).
% 7.82/1.48  
% 7.82/1.48  fof(f31,plain,(
% 7.82/1.48    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 7.82/1.48    inference(flattening,[],[f30])).
% 7.82/1.48  
% 7.82/1.48  fof(f44,plain,(
% 7.82/1.48    ( ! [X0,X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) => (k12_lattice3(X0,X1,k13_lattice3(X0,X1,sK4)) != X1 & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 7.82/1.48    introduced(choice_axiom,[])).
% 7.82/1.48  
% 7.82/1.48  fof(f43,plain,(
% 7.82/1.48    ( ! [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k12_lattice3(X0,sK3,k13_lattice3(X0,sK3,X2)) != sK3 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 7.82/1.48    introduced(choice_axiom,[])).
% 7.82/1.48  
% 7.82/1.48  fof(f42,plain,(
% 7.82/1.48    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => (? [X1] : (? [X2] : (k12_lattice3(sK2,X1,k13_lattice3(sK2,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_orders_2(sK2) & v2_lattice3(sK2) & v1_lattice3(sK2) & v5_orders_2(sK2) & v3_orders_2(sK2))),
% 7.82/1.48    introduced(choice_axiom,[])).
% 7.82/1.48  
% 7.82/1.48  fof(f45,plain,(
% 7.82/1.48    ((k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 & m1_subset_1(sK4,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_orders_2(sK2) & v2_lattice3(sK2) & v1_lattice3(sK2) & v5_orders_2(sK2) & v3_orders_2(sK2)),
% 7.82/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f31,f44,f43,f42])).
% 7.82/1.48  
% 7.82/1.48  fof(f69,plain,(
% 7.82/1.48    v1_lattice3(sK2)),
% 7.82/1.48    inference(cnf_transformation,[],[f45])).
% 7.82/1.48  
% 7.82/1.48  fof(f71,plain,(
% 7.82/1.48    l1_orders_2(sK2)),
% 7.82/1.48    inference(cnf_transformation,[],[f45])).
% 7.82/1.48  
% 7.82/1.48  fof(f68,plain,(
% 7.82/1.48    v5_orders_2(sK2)),
% 7.82/1.48    inference(cnf_transformation,[],[f45])).
% 7.82/1.48  
% 7.82/1.48  fof(f70,plain,(
% 7.82/1.48    v2_lattice3(sK2)),
% 7.82/1.48    inference(cnf_transformation,[],[f45])).
% 7.82/1.48  
% 7.82/1.48  fof(f63,plain,(
% 7.82/1.48    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,sK1(X0,X1,X2,X3),X3) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 7.82/1.48    inference(cnf_transformation,[],[f41])).
% 7.82/1.48  
% 7.82/1.48  fof(f72,plain,(
% 7.82/1.48    m1_subset_1(sK3,u1_struct_0(sK2))),
% 7.82/1.48    inference(cnf_transformation,[],[f45])).
% 7.82/1.48  
% 7.82/1.48  fof(f3,axiom,(
% 7.82/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 7.82/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.82/1.48  
% 7.82/1.48  fof(f16,plain,(
% 7.82/1.48    ! [X0,X1,X2] : (m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 7.82/1.48    inference(ennf_transformation,[],[f3])).
% 7.82/1.48  
% 7.82/1.48  fof(f17,plain,(
% 7.82/1.48    ! [X0,X1,X2] : (m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 7.82/1.48    inference(flattening,[],[f16])).
% 7.82/1.48  
% 7.82/1.48  fof(f48,plain,(
% 7.82/1.48    ( ! [X2,X0,X1] : (m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 7.82/1.48    inference(cnf_transformation,[],[f17])).
% 7.82/1.48  
% 7.82/1.48  fof(f8,axiom,(
% 7.82/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2))),
% 7.82/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.82/1.48  
% 7.82/1.48  fof(f26,plain,(
% 7.82/1.48    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 7.82/1.48    inference(ennf_transformation,[],[f8])).
% 7.82/1.48  
% 7.82/1.48  fof(f27,plain,(
% 7.82/1.48    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 7.82/1.48    inference(flattening,[],[f26])).
% 7.82/1.48  
% 7.82/1.48  fof(f65,plain,(
% 7.82/1.48    ( ! [X2,X0,X1] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 7.82/1.48    inference(cnf_transformation,[],[f27])).
% 7.82/1.48  
% 7.82/1.48  fof(f2,axiom,(
% 7.82/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k13_lattice3(X0,X1,X2) = k13_lattice3(X0,X2,X1))),
% 7.82/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.82/1.48  
% 7.82/1.48  fof(f14,plain,(
% 7.82/1.48    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k13_lattice3(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 7.82/1.48    inference(ennf_transformation,[],[f2])).
% 7.82/1.48  
% 7.82/1.48  fof(f15,plain,(
% 7.82/1.48    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k13_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 7.82/1.48    inference(flattening,[],[f14])).
% 7.82/1.48  
% 7.82/1.48  fof(f47,plain,(
% 7.82/1.48    ( ! [X2,X0,X1] : (k13_lattice3(X0,X1,X2) = k13_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 7.82/1.48    inference(cnf_transformation,[],[f15])).
% 7.82/1.48  
% 7.82/1.48  fof(f9,axiom,(
% 7.82/1.48    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2)))),
% 7.82/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.82/1.48  
% 7.82/1.48  fof(f28,plain,(
% 7.82/1.48    ! [X0] : (! [X1] : (! [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)))),
% 7.82/1.48    inference(ennf_transformation,[],[f9])).
% 7.82/1.48  
% 7.82/1.48  fof(f29,plain,(
% 7.82/1.48    ! [X0] : (! [X1] : (! [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 7.82/1.48    inference(flattening,[],[f28])).
% 7.82/1.48  
% 7.82/1.48  fof(f66,plain,(
% 7.82/1.48    ( ! [X2,X0,X1] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)) )),
% 7.82/1.48    inference(cnf_transformation,[],[f29])).
% 7.82/1.48  
% 7.82/1.48  fof(f67,plain,(
% 7.82/1.48    v3_orders_2(sK2)),
% 7.82/1.48    inference(cnf_transformation,[],[f45])).
% 7.82/1.48  
% 7.82/1.48  fof(f5,axiom,(
% 7.82/1.48    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 7.82/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.82/1.48  
% 7.82/1.48  fof(f20,plain,(
% 7.82/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 7.82/1.48    inference(ennf_transformation,[],[f5])).
% 7.82/1.48  
% 7.82/1.48  fof(f21,plain,(
% 7.82/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 7.82/1.48    inference(flattening,[],[f20])).
% 7.82/1.48  
% 7.82/1.48  fof(f32,plain,(
% 7.82/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3))) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 7.82/1.48    inference(nnf_transformation,[],[f21])).
% 7.82/1.48  
% 7.82/1.48  fof(f33,plain,(
% 7.82/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 7.82/1.48    inference(flattening,[],[f32])).
% 7.82/1.48  
% 7.82/1.48  fof(f34,plain,(
% 7.82/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 7.82/1.48    inference(rectify,[],[f33])).
% 7.82/1.48  
% 7.82/1.48  fof(f35,plain,(
% 7.82/1.48    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,X3,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))))),
% 7.82/1.48    introduced(choice_axiom,[])).
% 7.82/1.48  
% 7.82/1.48  fof(f36,plain,(
% 7.82/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,X3,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 7.82/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 7.82/1.48  
% 7.82/1.48  fof(f50,plain,(
% 7.82/1.48    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X1,X3) | k10_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 7.82/1.48    inference(cnf_transformation,[],[f36])).
% 7.82/1.48  
% 7.82/1.48  fof(f77,plain,(
% 7.82/1.48    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 7.82/1.48    inference(equality_resolution,[],[f50])).
% 7.82/1.48  
% 7.82/1.48  fof(f4,axiom,(
% 7.82/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 7.82/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.82/1.48  
% 7.82/1.48  fof(f18,plain,(
% 7.82/1.48    ! [X0,X1,X2] : (m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 7.82/1.48    inference(ennf_transformation,[],[f4])).
% 7.82/1.48  
% 7.82/1.48  fof(f19,plain,(
% 7.82/1.48    ! [X0,X1,X2] : (m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 7.82/1.48    inference(flattening,[],[f18])).
% 7.82/1.48  
% 7.82/1.48  fof(f49,plain,(
% 7.82/1.48    ( ! [X2,X0,X1] : (m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 7.82/1.48    inference(cnf_transformation,[],[f19])).
% 7.82/1.48  
% 7.82/1.48  fof(f73,plain,(
% 7.82/1.48    m1_subset_1(sK4,u1_struct_0(sK2))),
% 7.82/1.48    inference(cnf_transformation,[],[f45])).
% 7.82/1.48  
% 7.82/1.48  fof(f51,plain,(
% 7.82/1.48    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X2,X3) | k10_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 7.82/1.48    inference(cnf_transformation,[],[f36])).
% 7.82/1.48  
% 7.82/1.48  fof(f76,plain,(
% 7.82/1.48    ( ! [X2,X0,X1] : (r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 7.82/1.48    inference(equality_resolution,[],[f51])).
% 7.82/1.48  
% 7.82/1.48  fof(f7,axiom,(
% 7.82/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2))),
% 7.82/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.82/1.48  
% 7.82/1.48  fof(f24,plain,(
% 7.82/1.48    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 7.82/1.48    inference(ennf_transformation,[],[f7])).
% 7.82/1.48  
% 7.82/1.48  fof(f25,plain,(
% 7.82/1.48    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 7.82/1.48    inference(flattening,[],[f24])).
% 7.82/1.48  
% 7.82/1.48  fof(f64,plain,(
% 7.82/1.48    ( ! [X2,X0,X1] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 7.82/1.48    inference(cnf_transformation,[],[f25])).
% 7.82/1.48  
% 7.82/1.48  fof(f55,plain,(
% 7.82/1.48    ( ! [X2,X0,X3,X1] : (k10_lattice3(X0,X1,X2) = X3 | r1_orders_2(X0,X2,sK0(X0,X1,X2,X3)) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 7.82/1.48    inference(cnf_transformation,[],[f36])).
% 7.82/1.48  
% 7.82/1.48  fof(f56,plain,(
% 7.82/1.48    ( ! [X2,X0,X3,X1] : (k10_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,X3,sK0(X0,X1,X2,X3)) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 7.82/1.48    inference(cnf_transformation,[],[f36])).
% 7.82/1.48  
% 7.82/1.48  fof(f74,plain,(
% 7.82/1.48    k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3),
% 7.82/1.48    inference(cnf_transformation,[],[f45])).
% 7.82/1.48  
% 7.82/1.48  cnf(c_13,plain,
% 7.82/1.48      ( ~ r1_orders_2(X0,X1,X2)
% 7.82/1.48      | ~ r1_orders_2(X0,X1,X3)
% 7.82/1.48      | r1_orders_2(X0,sK1(X0,X3,X2,X1),X3)
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.82/1.48      | ~ v2_lattice3(X0)
% 7.82/1.48      | ~ v5_orders_2(X0)
% 7.82/1.48      | ~ l1_orders_2(X0)
% 7.82/1.48      | v2_struct_0(X0)
% 7.82/1.48      | k11_lattice3(X0,X3,X2) = X1 ),
% 7.82/1.48      inference(cnf_transformation,[],[f61]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_0,plain,
% 7.82/1.48      ( ~ l1_orders_2(X0) | ~ v1_lattice3(X0) | ~ v2_struct_0(X0) ),
% 7.82/1.48      inference(cnf_transformation,[],[f46]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_26,negated_conjecture,
% 7.82/1.48      ( v1_lattice3(sK2) ),
% 7.82/1.48      inference(cnf_transformation,[],[f69]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_568,plain,
% 7.82/1.48      ( ~ l1_orders_2(X0) | ~ v2_struct_0(X0) | sK2 != X0 ),
% 7.82/1.48      inference(resolution_lifted,[status(thm)],[c_0,c_26]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_569,plain,
% 7.82/1.48      ( ~ l1_orders_2(sK2) | ~ v2_struct_0(sK2) ),
% 7.82/1.48      inference(unflattening,[status(thm)],[c_568]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_24,negated_conjecture,
% 7.82/1.48      ( l1_orders_2(sK2) ),
% 7.82/1.48      inference(cnf_transformation,[],[f71]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_89,plain,
% 7.82/1.48      ( ~ l1_orders_2(sK2) | ~ v1_lattice3(sK2) | ~ v2_struct_0(sK2) ),
% 7.82/1.48      inference(instantiation,[status(thm)],[c_0]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_571,plain,
% 7.82/1.48      ( ~ v2_struct_0(sK2) ),
% 7.82/1.48      inference(global_propositional_subsumption,
% 7.82/1.48                [status(thm)],
% 7.82/1.48                [c_569,c_26,c_24,c_89]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_816,plain,
% 7.82/1.48      ( ~ r1_orders_2(X0,X1,X2)
% 7.82/1.48      | ~ r1_orders_2(X0,X1,X3)
% 7.82/1.48      | r1_orders_2(X0,sK1(X0,X2,X3,X1),X2)
% 7.82/1.48      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.82/1.48      | ~ v2_lattice3(X0)
% 7.82/1.48      | ~ v5_orders_2(X0)
% 7.82/1.48      | ~ l1_orders_2(X0)
% 7.82/1.48      | k11_lattice3(X0,X2,X3) = X1
% 7.82/1.48      | sK2 != X0 ),
% 7.82/1.48      inference(resolution_lifted,[status(thm)],[c_13,c_571]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_817,plain,
% 7.82/1.48      ( ~ r1_orders_2(sK2,X0,X1)
% 7.82/1.48      | ~ r1_orders_2(sK2,X0,X2)
% 7.82/1.48      | r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X1)
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 7.82/1.48      | ~ v2_lattice3(sK2)
% 7.82/1.48      | ~ v5_orders_2(sK2)
% 7.82/1.48      | ~ l1_orders_2(sK2)
% 7.82/1.48      | k11_lattice3(sK2,X1,X2) = X0 ),
% 7.82/1.48      inference(unflattening,[status(thm)],[c_816]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_27,negated_conjecture,
% 7.82/1.48      ( v5_orders_2(sK2) ),
% 7.82/1.48      inference(cnf_transformation,[],[f68]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_25,negated_conjecture,
% 7.82/1.48      ( v2_lattice3(sK2) ),
% 7.82/1.48      inference(cnf_transformation,[],[f70]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_821,plain,
% 7.82/1.48      ( ~ m1_subset_1(X2,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.82/1.48      | r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X1)
% 7.82/1.48      | ~ r1_orders_2(sK2,X0,X2)
% 7.82/1.48      | ~ r1_orders_2(sK2,X0,X1)
% 7.82/1.48      | k11_lattice3(sK2,X1,X2) = X0 ),
% 7.82/1.48      inference(global_propositional_subsumption,
% 7.82/1.48                [status(thm)],
% 7.82/1.48                [c_817,c_27,c_25,c_24]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_822,plain,
% 7.82/1.48      ( ~ r1_orders_2(sK2,X0,X1)
% 7.82/1.48      | ~ r1_orders_2(sK2,X0,X2)
% 7.82/1.48      | r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X1)
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.82/1.48      | k11_lattice3(sK2,X1,X2) = X0 ),
% 7.82/1.48      inference(renaming,[status(thm)],[c_821]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1159,plain,
% 7.82/1.48      ( ~ r1_orders_2(sK2,X0_46,X1_46)
% 7.82/1.48      | ~ r1_orders_2(sK2,X0_46,X2_46)
% 7.82/1.48      | r1_orders_2(sK2,sK1(sK2,X1_46,X2_46,X0_46),X1_46)
% 7.82/1.48      | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X2_46,u1_struct_0(sK2))
% 7.82/1.48      | k11_lattice3(sK2,X1_46,X2_46) = X0_46 ),
% 7.82/1.48      inference(subtyping,[status(esa)],[c_822]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_19599,plain,
% 7.82/1.48      ( ~ r1_orders_2(sK2,X0_46,k13_lattice3(sK2,sK3,sK4))
% 7.82/1.48      | ~ r1_orders_2(sK2,X0_46,sK3)
% 7.82/1.48      | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_46),sK3)
% 7.82/1.48      | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 7.82/1.48      | k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46 ),
% 7.82/1.48      inference(instantiation,[status(thm)],[c_1159]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_19616,plain,
% 7.82/1.48      ( r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),sK3),sK3)
% 7.82/1.48      | ~ r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
% 7.82/1.48      | ~ r1_orders_2(sK2,sK3,sK3)
% 7.82/1.48      | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 7.82/1.48      | k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3 ),
% 7.82/1.48      inference(instantiation,[status(thm)],[c_19599]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_11,plain,
% 7.82/1.48      ( ~ r1_orders_2(X0,X1,X2)
% 7.82/1.48      | ~ r1_orders_2(X0,X1,X3)
% 7.82/1.48      | ~ r1_orders_2(X0,sK1(X0,X3,X2,X1),X1)
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.82/1.48      | ~ v2_lattice3(X0)
% 7.82/1.48      | ~ v5_orders_2(X0)
% 7.82/1.48      | ~ l1_orders_2(X0)
% 7.82/1.48      | v2_struct_0(X0)
% 7.82/1.48      | k11_lattice3(X0,X3,X2) = X1 ),
% 7.82/1.48      inference(cnf_transformation,[],[f63]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_878,plain,
% 7.82/1.48      ( ~ r1_orders_2(X0,X1,X2)
% 7.82/1.48      | ~ r1_orders_2(X0,X1,X3)
% 7.82/1.48      | ~ r1_orders_2(X0,sK1(X0,X2,X3,X1),X1)
% 7.82/1.48      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.82/1.48      | ~ v2_lattice3(X0)
% 7.82/1.48      | ~ v5_orders_2(X0)
% 7.82/1.48      | ~ l1_orders_2(X0)
% 7.82/1.48      | k11_lattice3(X0,X2,X3) = X1
% 7.82/1.48      | sK2 != X0 ),
% 7.82/1.48      inference(resolution_lifted,[status(thm)],[c_11,c_571]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_879,plain,
% 7.82/1.48      ( ~ r1_orders_2(sK2,X0,X1)
% 7.82/1.48      | ~ r1_orders_2(sK2,X0,X2)
% 7.82/1.48      | ~ r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X0)
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 7.82/1.48      | ~ v2_lattice3(sK2)
% 7.82/1.48      | ~ v5_orders_2(sK2)
% 7.82/1.48      | ~ l1_orders_2(sK2)
% 7.82/1.48      | k11_lattice3(sK2,X1,X2) = X0 ),
% 7.82/1.48      inference(unflattening,[status(thm)],[c_878]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_883,plain,
% 7.82/1.48      ( ~ m1_subset_1(X2,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.82/1.48      | ~ r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X0)
% 7.82/1.48      | ~ r1_orders_2(sK2,X0,X2)
% 7.82/1.48      | ~ r1_orders_2(sK2,X0,X1)
% 7.82/1.48      | k11_lattice3(sK2,X1,X2) = X0 ),
% 7.82/1.48      inference(global_propositional_subsumption,
% 7.82/1.48                [status(thm)],
% 7.82/1.48                [c_879,c_27,c_25,c_24]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_884,plain,
% 7.82/1.48      ( ~ r1_orders_2(sK2,X0,X1)
% 7.82/1.48      | ~ r1_orders_2(sK2,X0,X2)
% 7.82/1.48      | ~ r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X0)
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.82/1.48      | k11_lattice3(sK2,X1,X2) = X0 ),
% 7.82/1.48      inference(renaming,[status(thm)],[c_883]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1157,plain,
% 7.82/1.48      ( ~ r1_orders_2(sK2,X0_46,X1_46)
% 7.82/1.48      | ~ r1_orders_2(sK2,X0_46,X2_46)
% 7.82/1.48      | ~ r1_orders_2(sK2,sK1(sK2,X1_46,X2_46,X0_46),X0_46)
% 7.82/1.48      | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X2_46,u1_struct_0(sK2))
% 7.82/1.48      | k11_lattice3(sK2,X1_46,X2_46) = X0_46 ),
% 7.82/1.48      inference(subtyping,[status(esa)],[c_884]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_19601,plain,
% 7.82/1.48      ( ~ r1_orders_2(sK2,X0_46,k13_lattice3(sK2,sK3,sK4))
% 7.82/1.48      | ~ r1_orders_2(sK2,X0_46,sK3)
% 7.82/1.48      | ~ r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_46),X0_46)
% 7.82/1.48      | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 7.82/1.48      | k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46 ),
% 7.82/1.48      inference(instantiation,[status(thm)],[c_1157]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_19608,plain,
% 7.82/1.48      ( ~ r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),sK3),sK3)
% 7.82/1.48      | ~ r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
% 7.82/1.48      | ~ r1_orders_2(sK2,sK3,sK3)
% 7.82/1.48      | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 7.82/1.48      | k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3 ),
% 7.82/1.48      inference(instantiation,[status(thm)],[c_19601]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1180,plain,
% 7.82/1.48      ( X0_46 != X1_46 | X2_46 != X1_46 | X2_46 = X0_46 ),
% 7.82/1.48      theory(equality) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_3332,plain,
% 7.82/1.48      ( X0_46 != X1_46
% 7.82/1.48      | X0_46 = k11_lattice3(sK2,X2_46,X3_46)
% 7.82/1.48      | k11_lattice3(sK2,X2_46,X3_46) != X1_46 ),
% 7.82/1.48      inference(instantiation,[status(thm)],[c_1180]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_14815,plain,
% 7.82/1.48      ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != X0_46
% 7.82/1.48      | sK3 != X0_46
% 7.82/1.48      | sK3 = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
% 7.82/1.48      inference(instantiation,[status(thm)],[c_3332]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_14816,plain,
% 7.82/1.48      ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3
% 7.82/1.48      | sK3 = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
% 7.82/1.48      | sK3 != sK3 ),
% 7.82/1.48      inference(instantiation,[status(thm)],[c_14815]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_23,negated_conjecture,
% 7.82/1.48      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 7.82/1.48      inference(cnf_transformation,[],[f72]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1175,negated_conjecture,
% 7.82/1.48      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 7.82/1.48      inference(subtyping,[status(esa)],[c_23]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1556,plain,
% 7.82/1.48      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 7.82/1.48      inference(predicate_to_equality,[status(thm)],[c_1175]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_2,plain,
% 7.82/1.48      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.82/1.48      | m1_subset_1(k12_lattice3(X1,X2,X0),u1_struct_0(X1))
% 7.82/1.48      | ~ v2_lattice3(X1)
% 7.82/1.48      | ~ v5_orders_2(X1)
% 7.82/1.48      | ~ l1_orders_2(X1) ),
% 7.82/1.48      inference(cnf_transformation,[],[f48]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_982,plain,
% 7.82/1.48      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.82/1.48      | m1_subset_1(k12_lattice3(X1,X2,X0),u1_struct_0(X1))
% 7.82/1.48      | ~ v2_lattice3(X1)
% 7.82/1.48      | ~ v5_orders_2(X1)
% 7.82/1.48      | sK2 != X1 ),
% 7.82/1.48      inference(resolution_lifted,[status(thm)],[c_2,c_24]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_983,plain,
% 7.82/1.48      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.82/1.48      | m1_subset_1(k12_lattice3(sK2,X0,X1),u1_struct_0(sK2))
% 7.82/1.48      | ~ v2_lattice3(sK2)
% 7.82/1.48      | ~ v5_orders_2(sK2) ),
% 7.82/1.48      inference(unflattening,[status(thm)],[c_982]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_987,plain,
% 7.82/1.48      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.82/1.48      | m1_subset_1(k12_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
% 7.82/1.48      inference(global_propositional_subsumption,
% 7.82/1.48                [status(thm)],
% 7.82/1.48                [c_983,c_27,c_25]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1155,plain,
% 7.82/1.48      ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 7.82/1.48      | m1_subset_1(k12_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) ),
% 7.82/1.48      inference(subtyping,[status(esa)],[c_987]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1576,plain,
% 7.82/1.48      ( m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 7.82/1.48      | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top
% 7.82/1.48      | m1_subset_1(k12_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) = iProver_top ),
% 7.82/1.48      inference(predicate_to_equality,[status(thm)],[c_1155]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_19,plain,
% 7.82/1.48      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.82/1.48      | ~ v5_orders_2(X1)
% 7.82/1.48      | ~ l1_orders_2(X1)
% 7.82/1.48      | ~ v1_lattice3(X1)
% 7.82/1.48      | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0) ),
% 7.82/1.48      inference(cnf_transformation,[],[f65]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_579,plain,
% 7.82/1.48      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.82/1.48      | ~ v5_orders_2(X1)
% 7.82/1.48      | ~ l1_orders_2(X1)
% 7.82/1.48      | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0)
% 7.82/1.48      | sK2 != X1 ),
% 7.82/1.48      inference(resolution_lifted,[status(thm)],[c_19,c_26]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_580,plain,
% 7.82/1.48      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.82/1.48      | ~ v5_orders_2(sK2)
% 7.82/1.48      | ~ l1_orders_2(sK2)
% 7.82/1.48      | k10_lattice3(sK2,X0,X1) = k13_lattice3(sK2,X0,X1) ),
% 7.82/1.48      inference(unflattening,[status(thm)],[c_579]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_584,plain,
% 7.82/1.48      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.82/1.48      | k10_lattice3(sK2,X0,X1) = k13_lattice3(sK2,X0,X1) ),
% 7.82/1.48      inference(global_propositional_subsumption,
% 7.82/1.48                [status(thm)],
% 7.82/1.48                [c_580,c_27,c_24]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1166,plain,
% 7.82/1.48      ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 7.82/1.48      | k10_lattice3(sK2,X0_46,X1_46) = k13_lattice3(sK2,X0_46,X1_46) ),
% 7.82/1.48      inference(subtyping,[status(esa)],[c_584]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1565,plain,
% 7.82/1.48      ( k10_lattice3(sK2,X0_46,X1_46) = k13_lattice3(sK2,X0_46,X1_46)
% 7.82/1.48      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 7.82/1.48      | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top ),
% 7.82/1.48      inference(predicate_to_equality,[status(thm)],[c_1166]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_2532,plain,
% 7.82/1.48      ( k10_lattice3(sK2,sK3,X0_46) = k13_lattice3(sK2,sK3,X0_46)
% 7.82/1.48      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top ),
% 7.82/1.48      inference(superposition,[status(thm)],[c_1556,c_1565]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_6614,plain,
% 7.82/1.48      ( k10_lattice3(sK2,sK3,k12_lattice3(sK2,X0_46,X1_46)) = k13_lattice3(sK2,sK3,k12_lattice3(sK2,X0_46,X1_46))
% 7.82/1.48      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 7.82/1.48      | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top ),
% 7.82/1.48      inference(superposition,[status(thm)],[c_1576,c_2532]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_11245,plain,
% 7.82/1.48      ( k10_lattice3(sK2,sK3,k12_lattice3(sK2,sK3,X0_46)) = k13_lattice3(sK2,sK3,k12_lattice3(sK2,sK3,X0_46))
% 7.82/1.48      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top ),
% 7.82/1.48      inference(superposition,[status(thm)],[c_1556,c_6614]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_11621,plain,
% 7.82/1.48      ( k10_lattice3(sK2,sK3,k12_lattice3(sK2,sK3,sK3)) = k13_lattice3(sK2,sK3,k12_lattice3(sK2,sK3,sK3)) ),
% 7.82/1.48      inference(superposition,[status(thm)],[c_1556,c_11245]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1,plain,
% 7.82/1.48      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.82/1.48      | ~ v5_orders_2(X1)
% 7.82/1.48      | ~ l1_orders_2(X1)
% 7.82/1.48      | ~ v1_lattice3(X1)
% 7.82/1.48      | k13_lattice3(X1,X0,X2) = k13_lattice3(X1,X2,X0) ),
% 7.82/1.48      inference(cnf_transformation,[],[f47]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_621,plain,
% 7.82/1.48      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.82/1.48      | ~ v5_orders_2(X1)
% 7.82/1.48      | ~ l1_orders_2(X1)
% 7.82/1.48      | k13_lattice3(X1,X2,X0) = k13_lattice3(X1,X0,X2)
% 7.82/1.48      | sK2 != X1 ),
% 7.82/1.48      inference(resolution_lifted,[status(thm)],[c_1,c_26]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_622,plain,
% 7.82/1.48      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.82/1.48      | ~ v5_orders_2(sK2)
% 7.82/1.48      | ~ l1_orders_2(sK2)
% 7.82/1.48      | k13_lattice3(sK2,X0,X1) = k13_lattice3(sK2,X1,X0) ),
% 7.82/1.48      inference(unflattening,[status(thm)],[c_621]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_626,plain,
% 7.82/1.48      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.82/1.48      | k13_lattice3(sK2,X0,X1) = k13_lattice3(sK2,X1,X0) ),
% 7.82/1.48      inference(global_propositional_subsumption,
% 7.82/1.48                [status(thm)],
% 7.82/1.48                [c_622,c_27,c_24]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1164,plain,
% 7.82/1.48      ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 7.82/1.48      | k13_lattice3(sK2,X0_46,X1_46) = k13_lattice3(sK2,X1_46,X0_46) ),
% 7.82/1.48      inference(subtyping,[status(esa)],[c_626]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1567,plain,
% 7.82/1.48      ( k13_lattice3(sK2,X0_46,X1_46) = k13_lattice3(sK2,X1_46,X0_46)
% 7.82/1.48      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 7.82/1.48      | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top ),
% 7.82/1.48      inference(predicate_to_equality,[status(thm)],[c_1164]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_3104,plain,
% 7.82/1.48      ( k13_lattice3(sK2,X0_46,sK3) = k13_lattice3(sK2,sK3,X0_46)
% 7.82/1.48      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top ),
% 7.82/1.48      inference(superposition,[status(thm)],[c_1556,c_1567]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_6611,plain,
% 7.82/1.48      ( k13_lattice3(sK2,k12_lattice3(sK2,X0_46,X1_46),sK3) = k13_lattice3(sK2,sK3,k12_lattice3(sK2,X0_46,X1_46))
% 7.82/1.48      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 7.82/1.48      | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top ),
% 7.82/1.48      inference(superposition,[status(thm)],[c_1576,c_3104]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_10502,plain,
% 7.82/1.48      ( k13_lattice3(sK2,sK3,k12_lattice3(sK2,sK3,X0_46)) = k13_lattice3(sK2,k12_lattice3(sK2,sK3,X0_46),sK3)
% 7.82/1.48      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top ),
% 7.82/1.48      inference(superposition,[status(thm)],[c_1556,c_6611]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_10828,plain,
% 7.82/1.48      ( k13_lattice3(sK2,sK3,k12_lattice3(sK2,sK3,sK3)) = k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK3),sK3) ),
% 7.82/1.48      inference(superposition,[status(thm)],[c_1556,c_10502]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_20,plain,
% 7.82/1.48      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.82/1.48      | ~ v3_orders_2(X1)
% 7.82/1.48      | ~ v2_lattice3(X1)
% 7.82/1.48      | ~ v5_orders_2(X1)
% 7.82/1.48      | ~ l1_orders_2(X1)
% 7.82/1.48      | ~ v1_lattice3(X1)
% 7.82/1.48      | k13_lattice3(X1,k12_lattice3(X1,X2,X0),X0) = X0 ),
% 7.82/1.48      inference(cnf_transformation,[],[f66]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_28,negated_conjecture,
% 7.82/1.48      ( v3_orders_2(sK2) ),
% 7.82/1.48      inference(cnf_transformation,[],[f67]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_338,plain,
% 7.82/1.48      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.82/1.48      | ~ v2_lattice3(X1)
% 7.82/1.48      | ~ v5_orders_2(X1)
% 7.82/1.48      | ~ l1_orders_2(X1)
% 7.82/1.48      | ~ v1_lattice3(X1)
% 7.82/1.48      | k13_lattice3(X1,k12_lattice3(X1,X2,X0),X0) = X0
% 7.82/1.48      | sK2 != X1 ),
% 7.82/1.48      inference(resolution_lifted,[status(thm)],[c_20,c_28]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_339,plain,
% 7.82/1.48      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.82/1.48      | ~ v2_lattice3(sK2)
% 7.82/1.48      | ~ v5_orders_2(sK2)
% 7.82/1.48      | ~ l1_orders_2(sK2)
% 7.82/1.48      | ~ v1_lattice3(sK2)
% 7.82/1.48      | k13_lattice3(sK2,k12_lattice3(sK2,X0,X1),X1) = X1 ),
% 7.82/1.48      inference(unflattening,[status(thm)],[c_338]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_343,plain,
% 7.82/1.48      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.82/1.48      | k13_lattice3(sK2,k12_lattice3(sK2,X0,X1),X1) = X1 ),
% 7.82/1.48      inference(global_propositional_subsumption,
% 7.82/1.48                [status(thm)],
% 7.82/1.48                [c_339,c_27,c_26,c_25,c_24]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1174,plain,
% 7.82/1.48      ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 7.82/1.48      | k13_lattice3(sK2,k12_lattice3(sK2,X0_46,X1_46),X1_46) = X1_46 ),
% 7.82/1.48      inference(subtyping,[status(esa)],[c_343]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1557,plain,
% 7.82/1.48      ( k13_lattice3(sK2,k12_lattice3(sK2,X0_46,X1_46),X1_46) = X1_46
% 7.82/1.48      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 7.82/1.48      | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top ),
% 7.82/1.48      inference(predicate_to_equality,[status(thm)],[c_1174]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1647,plain,
% 7.82/1.48      ( k13_lattice3(sK2,k12_lattice3(sK2,sK3,X0_46),X0_46) = X0_46
% 7.82/1.48      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top ),
% 7.82/1.48      inference(superposition,[status(thm)],[c_1556,c_1557]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1900,plain,
% 7.82/1.48      ( k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK3),sK3) = sK3 ),
% 7.82/1.48      inference(superposition,[status(thm)],[c_1556,c_1647]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_10833,plain,
% 7.82/1.48      ( k13_lattice3(sK2,sK3,k12_lattice3(sK2,sK3,sK3)) = sK3 ),
% 7.82/1.48      inference(light_normalisation,[status(thm)],[c_10828,c_1900]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_11626,plain,
% 7.82/1.48      ( k10_lattice3(sK2,sK3,k12_lattice3(sK2,sK3,sK3)) = sK3 ),
% 7.82/1.48      inference(light_normalisation,[status(thm)],[c_11621,c_10833]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_10,plain,
% 7.82/1.48      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 7.82/1.48      | ~ v5_orders_2(X0)
% 7.82/1.48      | ~ l1_orders_2(X0)
% 7.82/1.48      | ~ v1_lattice3(X0)
% 7.82/1.48      | v2_struct_0(X0) ),
% 7.82/1.48      inference(cnf_transformation,[],[f77]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_165,plain,
% 7.82/1.48      ( ~ v1_lattice3(X0)
% 7.82/1.48      | ~ l1_orders_2(X0)
% 7.82/1.48      | ~ v5_orders_2(X0)
% 7.82/1.48      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.82/1.48      | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) ),
% 7.82/1.48      inference(global_propositional_subsumption,
% 7.82/1.48                [status(thm)],
% 7.82/1.48                [c_10,c_0]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_166,plain,
% 7.82/1.48      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 7.82/1.48      | ~ v5_orders_2(X0)
% 7.82/1.48      | ~ l1_orders_2(X0)
% 7.82/1.48      | ~ v1_lattice3(X0) ),
% 7.82/1.48      inference(renaming,[status(thm)],[c_165]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_548,plain,
% 7.82/1.48      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 7.82/1.48      | ~ v5_orders_2(X0)
% 7.82/1.48      | ~ l1_orders_2(X0)
% 7.82/1.48      | sK2 != X0 ),
% 7.82/1.48      inference(resolution_lifted,[status(thm)],[c_166,c_26]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_549,plain,
% 7.82/1.48      ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2))
% 7.82/1.48      | ~ v5_orders_2(sK2)
% 7.82/1.48      | ~ l1_orders_2(sK2) ),
% 7.82/1.48      inference(unflattening,[status(thm)],[c_548]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_551,plain,
% 7.82/1.48      ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
% 7.82/1.48      inference(global_propositional_subsumption,
% 7.82/1.48                [status(thm)],
% 7.82/1.48                [c_549,c_27,c_24]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_552,plain,
% 7.82/1.48      ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
% 7.82/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
% 7.82/1.48      inference(renaming,[status(thm)],[c_551]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1167,plain,
% 7.82/1.48      ( r1_orders_2(sK2,X0_46,k10_lattice3(sK2,X0_46,X1_46))
% 7.82/1.48      | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(k10_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) ),
% 7.82/1.48      inference(subtyping,[status(esa)],[c_552]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1564,plain,
% 7.82/1.48      ( r1_orders_2(sK2,X0_46,k10_lattice3(sK2,X0_46,X1_46)) = iProver_top
% 7.82/1.48      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 7.82/1.48      | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top
% 7.82/1.48      | m1_subset_1(k10_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) != iProver_top ),
% 7.82/1.48      inference(predicate_to_equality,[status(thm)],[c_1167]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1212,plain,
% 7.82/1.48      ( r1_orders_2(sK2,X0_46,k10_lattice3(sK2,X0_46,X1_46)) = iProver_top
% 7.82/1.48      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 7.82/1.48      | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top
% 7.82/1.48      | m1_subset_1(k10_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) != iProver_top ),
% 7.82/1.48      inference(predicate_to_equality,[status(thm)],[c_1167]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1213,plain,
% 7.82/1.48      ( k10_lattice3(sK2,X0_46,X1_46) = k13_lattice3(sK2,X0_46,X1_46)
% 7.82/1.48      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 7.82/1.48      | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top ),
% 7.82/1.48      inference(predicate_to_equality,[status(thm)],[c_1166]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_3,plain,
% 7.82/1.48      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.82/1.48      | m1_subset_1(k13_lattice3(X1,X2,X0),u1_struct_0(X1))
% 7.82/1.48      | ~ v5_orders_2(X1)
% 7.82/1.48      | ~ l1_orders_2(X1)
% 7.82/1.48      | ~ v1_lattice3(X1) ),
% 7.82/1.48      inference(cnf_transformation,[],[f49]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_600,plain,
% 7.82/1.48      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.82/1.48      | m1_subset_1(k13_lattice3(X1,X2,X0),u1_struct_0(X1))
% 7.82/1.48      | ~ v5_orders_2(X1)
% 7.82/1.48      | ~ l1_orders_2(X1)
% 7.82/1.48      | sK2 != X1 ),
% 7.82/1.48      inference(resolution_lifted,[status(thm)],[c_3,c_26]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_601,plain,
% 7.82/1.48      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.82/1.48      | m1_subset_1(k13_lattice3(sK2,X0,X1),u1_struct_0(sK2))
% 7.82/1.48      | ~ v5_orders_2(sK2)
% 7.82/1.48      | ~ l1_orders_2(sK2) ),
% 7.82/1.48      inference(unflattening,[status(thm)],[c_600]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_605,plain,
% 7.82/1.48      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.82/1.48      | m1_subset_1(k13_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
% 7.82/1.48      inference(global_propositional_subsumption,
% 7.82/1.48                [status(thm)],
% 7.82/1.48                [c_601,c_27,c_24]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1165,plain,
% 7.82/1.48      ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 7.82/1.48      | m1_subset_1(k13_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) ),
% 7.82/1.48      inference(subtyping,[status(esa)],[c_605]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1216,plain,
% 7.82/1.48      ( m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 7.82/1.48      | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top
% 7.82/1.48      | m1_subset_1(k13_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) = iProver_top ),
% 7.82/1.48      inference(predicate_to_equality,[status(thm)],[c_1165]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1182,plain,
% 7.82/1.48      ( ~ m1_subset_1(X0_46,X0_47)
% 7.82/1.48      | m1_subset_1(X1_46,X0_47)
% 7.82/1.48      | X1_46 != X0_46 ),
% 7.82/1.48      theory(equality) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1622,plain,
% 7.82/1.48      ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 7.82/1.48      | m1_subset_1(k10_lattice3(sK2,X1_46,X2_46),u1_struct_0(sK2))
% 7.82/1.48      | k10_lattice3(sK2,X1_46,X2_46) != X0_46 ),
% 7.82/1.48      inference(instantiation,[status(thm)],[c_1182]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1659,plain,
% 7.82/1.48      ( m1_subset_1(k10_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(k13_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2))
% 7.82/1.48      | k10_lattice3(sK2,X0_46,X1_46) != k13_lattice3(sK2,X0_46,X1_46) ),
% 7.82/1.48      inference(instantiation,[status(thm)],[c_1622]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1660,plain,
% 7.82/1.48      ( k10_lattice3(sK2,X0_46,X1_46) != k13_lattice3(sK2,X0_46,X1_46)
% 7.82/1.48      | m1_subset_1(k10_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) = iProver_top
% 7.82/1.48      | m1_subset_1(k13_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) != iProver_top ),
% 7.82/1.48      inference(predicate_to_equality,[status(thm)],[c_1659]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_6992,plain,
% 7.82/1.48      ( m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top
% 7.82/1.48      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 7.82/1.48      | r1_orders_2(sK2,X0_46,k10_lattice3(sK2,X0_46,X1_46)) = iProver_top ),
% 7.82/1.48      inference(global_propositional_subsumption,
% 7.82/1.48                [status(thm)],
% 7.82/1.48                [c_1564,c_1212,c_1213,c_1216,c_1660]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_6993,plain,
% 7.82/1.48      ( r1_orders_2(sK2,X0_46,k10_lattice3(sK2,X0_46,X1_46)) = iProver_top
% 7.82/1.48      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 7.82/1.48      | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top ),
% 7.82/1.48      inference(renaming,[status(thm)],[c_6992]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_11795,plain,
% 7.82/1.48      ( r1_orders_2(sK2,sK3,sK3) = iProver_top
% 7.82/1.48      | m1_subset_1(k12_lattice3(sK2,sK3,sK3),u1_struct_0(sK2)) != iProver_top
% 7.82/1.48      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 7.82/1.48      inference(superposition,[status(thm)],[c_11626,c_6993]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1621,plain,
% 7.82/1.48      ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != X0_46
% 7.82/1.48      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
% 7.82/1.48      | sK3 != X0_46 ),
% 7.82/1.48      inference(instantiation,[status(thm)],[c_1180]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_7602,plain,
% 7.82/1.48      ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
% 7.82/1.48      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
% 7.82/1.48      | sK3 != k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
% 7.82/1.48      inference(instantiation,[status(thm)],[c_1621]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_22,negated_conjecture,
% 7.82/1.48      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 7.82/1.48      inference(cnf_transformation,[],[f73]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1176,negated_conjecture,
% 7.82/1.48      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 7.82/1.48      inference(subtyping,[status(esa)],[c_22]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1555,plain,
% 7.82/1.48      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 7.82/1.48      inference(predicate_to_equality,[status(thm)],[c_1176]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_3103,plain,
% 7.82/1.48      ( k13_lattice3(sK2,X0_46,sK4) = k13_lattice3(sK2,sK4,X0_46)
% 7.82/1.48      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top ),
% 7.82/1.48      inference(superposition,[status(thm)],[c_1555,c_1567]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_3155,plain,
% 7.82/1.48      ( k13_lattice3(sK2,sK4,sK3) = k13_lattice3(sK2,sK3,sK4) ),
% 7.82/1.48      inference(superposition,[status(thm)],[c_1556,c_3103]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_2531,plain,
% 7.82/1.48      ( k10_lattice3(sK2,sK4,X0_46) = k13_lattice3(sK2,sK4,X0_46)
% 7.82/1.48      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top ),
% 7.82/1.48      inference(superposition,[status(thm)],[c_1555,c_1565]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_2817,plain,
% 7.82/1.48      ( k10_lattice3(sK2,sK4,sK3) = k13_lattice3(sK2,sK4,sK3) ),
% 7.82/1.48      inference(superposition,[status(thm)],[c_1556,c_2531]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_3224,plain,
% 7.82/1.48      ( k10_lattice3(sK2,sK4,sK3) = k13_lattice3(sK2,sK3,sK4) ),
% 7.82/1.48      inference(demodulation,[status(thm)],[c_3155,c_2817]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_9,plain,
% 7.82/1.48      ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
% 7.82/1.48      | ~ v5_orders_2(X0)
% 7.82/1.48      | ~ l1_orders_2(X0)
% 7.82/1.48      | ~ v1_lattice3(X0)
% 7.82/1.48      | v2_struct_0(X0) ),
% 7.82/1.48      inference(cnf_transformation,[],[f76]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_172,plain,
% 7.82/1.48      ( ~ v1_lattice3(X0)
% 7.82/1.48      | ~ l1_orders_2(X0)
% 7.82/1.48      | ~ v5_orders_2(X0)
% 7.82/1.48      | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.82/1.48      | r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1)) ),
% 7.82/1.48      inference(global_propositional_subsumption,[status(thm)],[c_9,c_0]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_173,plain,
% 7.82/1.48      ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
% 7.82/1.48      | ~ v5_orders_2(X0)
% 7.82/1.48      | ~ l1_orders_2(X0)
% 7.82/1.48      | ~ v1_lattice3(X0) ),
% 7.82/1.48      inference(renaming,[status(thm)],[c_172]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_524,plain,
% 7.82/1.48      ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
% 7.82/1.48      | ~ v5_orders_2(X0)
% 7.82/1.48      | ~ l1_orders_2(X0)
% 7.82/1.48      | sK2 != X0 ),
% 7.82/1.48      inference(resolution_lifted,[status(thm)],[c_173,c_26]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_525,plain,
% 7.82/1.48      ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X1,X0))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(k10_lattice3(sK2,X1,X0),u1_struct_0(sK2))
% 7.82/1.48      | ~ v5_orders_2(sK2)
% 7.82/1.48      | ~ l1_orders_2(sK2) ),
% 7.82/1.48      inference(unflattening,[status(thm)],[c_524]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_529,plain,
% 7.82/1.48      ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X1,X0))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(k10_lattice3(sK2,X1,X0),u1_struct_0(sK2)) ),
% 7.82/1.48      inference(global_propositional_subsumption,
% 7.82/1.48                [status(thm)],
% 7.82/1.48                [c_525,c_27,c_24]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_530,plain,
% 7.82/1.48      ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X1,X0))
% 7.82/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(k10_lattice3(sK2,X1,X0),u1_struct_0(sK2)) ),
% 7.82/1.48      inference(renaming,[status(thm)],[c_529]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1168,plain,
% 7.82/1.48      ( r1_orders_2(sK2,X0_46,k10_lattice3(sK2,X1_46,X0_46))
% 7.82/1.48      | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(k10_lattice3(sK2,X1_46,X0_46),u1_struct_0(sK2)) ),
% 7.82/1.48      inference(subtyping,[status(esa)],[c_530]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1563,plain,
% 7.82/1.48      ( r1_orders_2(sK2,X0_46,k10_lattice3(sK2,X1_46,X0_46)) = iProver_top
% 7.82/1.48      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 7.82/1.48      | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top
% 7.82/1.48      | m1_subset_1(k10_lattice3(sK2,X1_46,X0_46),u1_struct_0(sK2)) != iProver_top ),
% 7.82/1.48      inference(predicate_to_equality,[status(thm)],[c_1168]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_6971,plain,
% 7.82/1.48      ( r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK4,sK3)) = iProver_top
% 7.82/1.48      | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 7.82/1.48      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 7.82/1.48      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 7.82/1.48      inference(superposition,[status(thm)],[c_3224,c_1563]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_6982,plain,
% 7.82/1.48      ( r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = iProver_top
% 7.82/1.48      | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 7.82/1.48      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 7.82/1.48      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 7.82/1.48      inference(light_normalisation,[status(thm)],[c_6971,c_3224]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_6989,plain,
% 7.82/1.48      ( r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
% 7.82/1.48      | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 7.82/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_6982]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_6555,plain,
% 7.82/1.48      ( m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 7.82/1.48      inference(instantiation,[status(thm)],[c_1165]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_18,plain,
% 7.82/1.48      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.82/1.48      | ~ v2_lattice3(X1)
% 7.82/1.48      | ~ v5_orders_2(X1)
% 7.82/1.48      | ~ l1_orders_2(X1)
% 7.82/1.48      | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0) ),
% 7.82/1.48      inference(cnf_transformation,[],[f64]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_961,plain,
% 7.82/1.48      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.82/1.48      | ~ v2_lattice3(X1)
% 7.82/1.48      | ~ v5_orders_2(X1)
% 7.82/1.48      | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0)
% 7.82/1.48      | sK2 != X1 ),
% 7.82/1.48      inference(resolution_lifted,[status(thm)],[c_18,c_24]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_962,plain,
% 7.82/1.48      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.82/1.48      | ~ v2_lattice3(sK2)
% 7.82/1.48      | ~ v5_orders_2(sK2)
% 7.82/1.48      | k11_lattice3(sK2,X0,X1) = k12_lattice3(sK2,X0,X1) ),
% 7.82/1.48      inference(unflattening,[status(thm)],[c_961]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_966,plain,
% 7.82/1.48      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.82/1.48      | k11_lattice3(sK2,X0,X1) = k12_lattice3(sK2,X0,X1) ),
% 7.82/1.48      inference(global_propositional_subsumption,
% 7.82/1.48                [status(thm)],
% 7.82/1.48                [c_962,c_27,c_25]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1156,plain,
% 7.82/1.48      ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 7.82/1.48      | k11_lattice3(sK2,X0_46,X1_46) = k12_lattice3(sK2,X0_46,X1_46) ),
% 7.82/1.48      inference(subtyping,[status(esa)],[c_966]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_6053,plain,
% 7.82/1.48      ( ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 7.82/1.48      | k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
% 7.82/1.48      inference(instantiation,[status(thm)],[c_1156]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1656,plain,
% 7.82/1.48      ( X0_46 != X1_46
% 7.82/1.48      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != X1_46
% 7.82/1.48      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46 ),
% 7.82/1.48      inference(instantiation,[status(thm)],[c_1180]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1678,plain,
% 7.82/1.48      ( X0_46 != k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
% 7.82/1.48      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46
% 7.82/1.48      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
% 7.82/1.48      inference(instantiation,[status(thm)],[c_1656]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_6052,plain,
% 7.82/1.48      ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
% 7.82/1.48      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
% 7.82/1.48      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
% 7.82/1.48      inference(instantiation,[status(thm)],[c_1678]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_5,plain,
% 7.82/1.48      ( ~ r1_orders_2(X0,X1,X2)
% 7.82/1.48      | ~ r1_orders_2(X0,X3,X2)
% 7.82/1.48      | r1_orders_2(X0,X1,sK0(X0,X3,X1,X2))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.82/1.48      | ~ v5_orders_2(X0)
% 7.82/1.48      | ~ l1_orders_2(X0)
% 7.82/1.48      | ~ v1_lattice3(X0)
% 7.82/1.48      | v2_struct_0(X0)
% 7.82/1.48      | k10_lattice3(X0,X3,X1) = X2 ),
% 7.82/1.48      inference(cnf_transformation,[],[f55]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_198,plain,
% 7.82/1.48      ( ~ v1_lattice3(X0)
% 7.82/1.48      | ~ l1_orders_2(X0)
% 7.82/1.48      | ~ v5_orders_2(X0)
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.82/1.48      | r1_orders_2(X0,X1,sK0(X0,X3,X1,X2))
% 7.82/1.48      | ~ r1_orders_2(X0,X3,X2)
% 7.82/1.48      | ~ r1_orders_2(X0,X1,X2)
% 7.82/1.48      | k10_lattice3(X0,X3,X1) = X2 ),
% 7.82/1.48      inference(global_propositional_subsumption,[status(thm)],[c_5,c_0]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_199,plain,
% 7.82/1.48      ( ~ r1_orders_2(X0,X1,X2)
% 7.82/1.48      | ~ r1_orders_2(X0,X3,X2)
% 7.82/1.48      | r1_orders_2(X0,X1,sK0(X0,X3,X1,X2))
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.82/1.48      | ~ v5_orders_2(X0)
% 7.82/1.48      | ~ l1_orders_2(X0)
% 7.82/1.48      | ~ v1_lattice3(X0)
% 7.82/1.48      | k10_lattice3(X0,X3,X1) = X2 ),
% 7.82/1.48      inference(renaming,[status(thm)],[c_198]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_396,plain,
% 7.82/1.48      ( ~ r1_orders_2(X0,X1,X2)
% 7.82/1.48      | ~ r1_orders_2(X0,X3,X2)
% 7.82/1.48      | r1_orders_2(X0,X1,sK0(X0,X3,X1,X2))
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.82/1.48      | ~ v5_orders_2(X0)
% 7.82/1.48      | ~ l1_orders_2(X0)
% 7.82/1.48      | k10_lattice3(X0,X3,X1) = X2
% 7.82/1.48      | sK2 != X0 ),
% 7.82/1.48      inference(resolution_lifted,[status(thm)],[c_199,c_26]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_397,plain,
% 7.82/1.48      ( ~ r1_orders_2(sK2,X0,X1)
% 7.82/1.48      | ~ r1_orders_2(sK2,X2,X1)
% 7.82/1.48      | r1_orders_2(sK2,X2,sK0(sK2,X0,X2,X1))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.82/1.48      | ~ v5_orders_2(sK2)
% 7.82/1.48      | ~ l1_orders_2(sK2)
% 7.82/1.48      | k10_lattice3(sK2,X0,X2) = X1 ),
% 7.82/1.48      inference(unflattening,[status(thm)],[c_396]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_401,plain,
% 7.82/1.48      ( ~ r1_orders_2(sK2,X0,X1)
% 7.82/1.48      | ~ r1_orders_2(sK2,X2,X1)
% 7.82/1.48      | r1_orders_2(sK2,X2,sK0(sK2,X0,X2,X1))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.82/1.48      | k10_lattice3(sK2,X0,X2) = X1 ),
% 7.82/1.48      inference(global_propositional_subsumption,
% 7.82/1.48                [status(thm)],
% 7.82/1.48                [c_397,c_27,c_24]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_402,plain,
% 7.82/1.48      ( ~ r1_orders_2(sK2,X0,X1)
% 7.82/1.48      | ~ r1_orders_2(sK2,X2,X1)
% 7.82/1.48      | r1_orders_2(sK2,X2,sK0(sK2,X0,X2,X1))
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.82/1.48      | k10_lattice3(sK2,X0,X2) = X1 ),
% 7.82/1.48      inference(renaming,[status(thm)],[c_401]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1172,plain,
% 7.82/1.48      ( ~ r1_orders_2(sK2,X0_46,X1_46)
% 7.82/1.48      | ~ r1_orders_2(sK2,X2_46,X1_46)
% 7.82/1.48      | r1_orders_2(sK2,X2_46,sK0(sK2,X0_46,X2_46,X1_46))
% 7.82/1.48      | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X2_46,u1_struct_0(sK2))
% 7.82/1.48      | k10_lattice3(sK2,X0_46,X2_46) = X1_46 ),
% 7.82/1.48      inference(subtyping,[status(esa)],[c_402]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1559,plain,
% 7.82/1.48      ( k10_lattice3(sK2,X0_46,X1_46) = X2_46
% 7.82/1.48      | r1_orders_2(sK2,X0_46,X2_46) != iProver_top
% 7.82/1.48      | r1_orders_2(sK2,X1_46,X2_46) != iProver_top
% 7.82/1.48      | r1_orders_2(sK2,X1_46,sK0(sK2,X0_46,X1_46,X2_46)) = iProver_top
% 7.82/1.48      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 7.82/1.48      | m1_subset_1(X2_46,u1_struct_0(sK2)) != iProver_top
% 7.82/1.48      | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top ),
% 7.82/1.48      inference(predicate_to_equality,[status(thm)],[c_1172]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_4,plain,
% 7.82/1.48      ( ~ r1_orders_2(X0,X1,X2)
% 7.82/1.48      | ~ r1_orders_2(X0,X3,X2)
% 7.82/1.48      | ~ r1_orders_2(X0,X2,sK0(X0,X3,X1,X2))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.82/1.48      | ~ v5_orders_2(X0)
% 7.82/1.48      | ~ l1_orders_2(X0)
% 7.82/1.48      | ~ v1_lattice3(X0)
% 7.82/1.48      | v2_struct_0(X0)
% 7.82/1.48      | k10_lattice3(X0,X3,X1) = X2 ),
% 7.82/1.48      inference(cnf_transformation,[],[f56]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_203,plain,
% 7.82/1.48      ( ~ v1_lattice3(X0)
% 7.82/1.48      | ~ l1_orders_2(X0)
% 7.82/1.48      | ~ v5_orders_2(X0)
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.82/1.48      | ~ r1_orders_2(X0,X2,sK0(X0,X3,X1,X2))
% 7.82/1.48      | ~ r1_orders_2(X0,X3,X2)
% 7.82/1.48      | ~ r1_orders_2(X0,X1,X2)
% 7.82/1.48      | k10_lattice3(X0,X3,X1) = X2 ),
% 7.82/1.48      inference(global_propositional_subsumption,[status(thm)],[c_4,c_0]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_204,plain,
% 7.82/1.48      ( ~ r1_orders_2(X0,X1,X2)
% 7.82/1.48      | ~ r1_orders_2(X0,X3,X2)
% 7.82/1.48      | ~ r1_orders_2(X0,X2,sK0(X0,X3,X1,X2))
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.82/1.48      | ~ v5_orders_2(X0)
% 7.82/1.48      | ~ l1_orders_2(X0)
% 7.82/1.48      | ~ v1_lattice3(X0)
% 7.82/1.48      | k10_lattice3(X0,X3,X1) = X2 ),
% 7.82/1.48      inference(renaming,[status(thm)],[c_203]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_363,plain,
% 7.82/1.48      ( ~ r1_orders_2(X0,X1,X2)
% 7.82/1.48      | ~ r1_orders_2(X0,X3,X2)
% 7.82/1.48      | ~ r1_orders_2(X0,X2,sK0(X0,X3,X1,X2))
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.82/1.48      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.82/1.48      | ~ v5_orders_2(X0)
% 7.82/1.48      | ~ l1_orders_2(X0)
% 7.82/1.48      | k10_lattice3(X0,X3,X1) = X2
% 7.82/1.48      | sK2 != X0 ),
% 7.82/1.48      inference(resolution_lifted,[status(thm)],[c_204,c_26]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_364,plain,
% 7.82/1.48      ( ~ r1_orders_2(sK2,X0,X1)
% 7.82/1.48      | ~ r1_orders_2(sK2,X2,X1)
% 7.82/1.48      | ~ r1_orders_2(sK2,X1,sK0(sK2,X0,X2,X1))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.82/1.48      | ~ v5_orders_2(sK2)
% 7.82/1.48      | ~ l1_orders_2(sK2)
% 7.82/1.48      | k10_lattice3(sK2,X0,X2) = X1 ),
% 7.82/1.48      inference(unflattening,[status(thm)],[c_363]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_368,plain,
% 7.82/1.48      ( ~ r1_orders_2(sK2,X0,X1)
% 7.82/1.48      | ~ r1_orders_2(sK2,X2,X1)
% 7.82/1.48      | ~ r1_orders_2(sK2,X1,sK0(sK2,X0,X2,X1))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.82/1.48      | k10_lattice3(sK2,X0,X2) = X1 ),
% 7.82/1.48      inference(global_propositional_subsumption,
% 7.82/1.48                [status(thm)],
% 7.82/1.48                [c_364,c_27,c_24]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_369,plain,
% 7.82/1.48      ( ~ r1_orders_2(sK2,X0,X1)
% 7.82/1.48      | ~ r1_orders_2(sK2,X2,X1)
% 7.82/1.48      | ~ r1_orders_2(sK2,X1,sK0(sK2,X0,X2,X1))
% 7.82/1.48      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.82/1.48      | k10_lattice3(sK2,X0,X2) = X1 ),
% 7.82/1.48      inference(renaming,[status(thm)],[c_368]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1173,plain,
% 7.82/1.48      ( ~ r1_orders_2(sK2,X0_46,X1_46)
% 7.82/1.48      | ~ r1_orders_2(sK2,X2_46,X1_46)
% 7.82/1.48      | ~ r1_orders_2(sK2,X1_46,sK0(sK2,X0_46,X2_46,X1_46))
% 7.82/1.48      | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(X2_46,u1_struct_0(sK2))
% 7.82/1.48      | k10_lattice3(sK2,X0_46,X2_46) = X1_46 ),
% 7.82/1.48      inference(subtyping,[status(esa)],[c_369]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1558,plain,
% 7.82/1.48      ( k10_lattice3(sK2,X0_46,X1_46) = X2_46
% 7.82/1.48      | r1_orders_2(sK2,X0_46,X2_46) != iProver_top
% 7.82/1.48      | r1_orders_2(sK2,X1_46,X2_46) != iProver_top
% 7.82/1.48      | r1_orders_2(sK2,X2_46,sK0(sK2,X0_46,X1_46,X2_46)) != iProver_top
% 7.82/1.48      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 7.82/1.48      | m1_subset_1(X2_46,u1_struct_0(sK2)) != iProver_top
% 7.82/1.48      | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top ),
% 7.82/1.48      inference(predicate_to_equality,[status(thm)],[c_1173]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_3161,plain,
% 7.82/1.48      ( k10_lattice3(sK2,X0_46,X1_46) = X1_46
% 7.82/1.48      | r1_orders_2(sK2,X0_46,X1_46) != iProver_top
% 7.82/1.48      | r1_orders_2(sK2,X1_46,X1_46) != iProver_top
% 7.82/1.48      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 7.82/1.48      | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top ),
% 7.82/1.48      inference(superposition,[status(thm)],[c_1559,c_1558]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_3163,plain,
% 7.82/1.48      ( k10_lattice3(sK2,sK3,sK3) = sK3
% 7.82/1.48      | r1_orders_2(sK2,sK3,sK3) != iProver_top
% 7.82/1.48      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 7.82/1.48      inference(instantiation,[status(thm)],[c_3161]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1179,plain,( X0_46 = X0_46 ),theory(equality) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_2938,plain,
% 7.82/1.48      ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
% 7.82/1.48      inference(instantiation,[status(thm)],[c_1179]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1879,plain,
% 7.82/1.48      ( X0_46 != X1_46
% 7.82/1.48      | X0_46 = k10_lattice3(sK2,X2_46,X3_46)
% 7.82/1.48      | k10_lattice3(sK2,X2_46,X3_46) != X1_46 ),
% 7.82/1.48      inference(instantiation,[status(thm)],[c_1180]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1880,plain,
% 7.82/1.48      ( k10_lattice3(sK2,sK3,sK3) != sK3
% 7.82/1.48      | sK3 = k10_lattice3(sK2,sK3,sK3)
% 7.82/1.48      | sK3 != sK3 ),
% 7.82/1.48      inference(instantiation,[status(thm)],[c_1879]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1184,plain,
% 7.82/1.48      ( ~ r1_orders_2(X0_48,X0_46,X1_46)
% 7.82/1.48      | r1_orders_2(X0_48,X2_46,X3_46)
% 7.82/1.48      | X2_46 != X0_46
% 7.82/1.48      | X3_46 != X1_46 ),
% 7.82/1.48      theory(equality) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1629,plain,
% 7.82/1.48      ( ~ r1_orders_2(sK2,X0_46,X1_46)
% 7.82/1.48      | r1_orders_2(sK2,X2_46,X3_46)
% 7.82/1.48      | X2_46 != X0_46
% 7.82/1.48      | X3_46 != X1_46 ),
% 7.82/1.48      inference(instantiation,[status(thm)],[c_1184]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1683,plain,
% 7.82/1.48      ( r1_orders_2(sK2,X0_46,X1_46)
% 7.82/1.48      | ~ r1_orders_2(sK2,X2_46,k10_lattice3(sK2,X2_46,X3_46))
% 7.82/1.48      | X0_46 != X2_46
% 7.82/1.48      | X1_46 != k10_lattice3(sK2,X2_46,X3_46) ),
% 7.82/1.48      inference(instantiation,[status(thm)],[c_1629]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1733,plain,
% 7.82/1.48      ( ~ r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK3))
% 7.82/1.48      | r1_orders_2(sK2,sK3,sK3)
% 7.82/1.48      | sK3 != k10_lattice3(sK2,sK3,sK3)
% 7.82/1.48      | sK3 != sK3 ),
% 7.82/1.48      inference(instantiation,[status(thm)],[c_1683]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1661,plain,
% 7.82/1.48      ( m1_subset_1(k10_lattice3(sK2,sK3,sK3),u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK3),u1_struct_0(sK2))
% 7.82/1.48      | k10_lattice3(sK2,sK3,sK3) != k13_lattice3(sK2,sK3,sK3) ),
% 7.82/1.48      inference(instantiation,[status(thm)],[c_1659]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1242,plain,
% 7.82/1.48      ( m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 7.82/1.48      | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top
% 7.82/1.48      | m1_subset_1(k12_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) = iProver_top ),
% 7.82/1.48      inference(predicate_to_equality,[status(thm)],[c_1155]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1244,plain,
% 7.82/1.48      ( m1_subset_1(k12_lattice3(sK2,sK3,sK3),u1_struct_0(sK2)) = iProver_top
% 7.82/1.48      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 7.82/1.48      inference(instantiation,[status(thm)],[c_1242]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1217,plain,
% 7.82/1.48      ( m1_subset_1(k13_lattice3(sK2,sK3,sK3),u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 7.82/1.48      inference(instantiation,[status(thm)],[c_1165]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1214,plain,
% 7.82/1.48      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 7.82/1.48      | k10_lattice3(sK2,sK3,sK3) = k13_lattice3(sK2,sK3,sK3) ),
% 7.82/1.48      inference(instantiation,[status(thm)],[c_1166]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1210,plain,
% 7.82/1.48      ( r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK3))
% 7.82/1.48      | ~ m1_subset_1(k10_lattice3(sK2,sK3,sK3),u1_struct_0(sK2))
% 7.82/1.48      | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 7.82/1.48      inference(instantiation,[status(thm)],[c_1168]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_21,negated_conjecture,
% 7.82/1.48      ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
% 7.82/1.48      inference(cnf_transformation,[],[f74]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1177,negated_conjecture,
% 7.82/1.48      ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
% 7.82/1.48      inference(subtyping,[status(esa)],[c_21]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1190,plain,
% 7.82/1.48      ( sK3 = sK3 ),
% 7.82/1.48      inference(instantiation,[status(thm)],[c_1179]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_34,plain,
% 7.82/1.48      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 7.82/1.48      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(contradiction,plain,
% 7.82/1.48      ( $false ),
% 7.82/1.48      inference(minisat,
% 7.82/1.48                [status(thm)],
% 7.82/1.48                [c_19616,c_19608,c_14816,c_11795,c_7602,c_6989,c_6555,
% 7.82/1.48                 c_6053,c_6052,c_3163,c_2938,c_1880,c_1733,c_1661,c_1244,
% 7.82/1.48                 c_1217,c_1214,c_1210,c_1177,c_1190,c_22,c_34,c_23]) ).
% 7.82/1.48  
% 7.82/1.48  
% 7.82/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.82/1.48  
% 7.82/1.48  ------                               Statistics
% 7.82/1.48  
% 7.82/1.48  ------ General
% 7.82/1.48  
% 7.82/1.48  abstr_ref_over_cycles:                  0
% 7.82/1.48  abstr_ref_under_cycles:                 0
% 7.82/1.48  gc_basic_clause_elim:                   0
% 7.82/1.48  forced_gc_time:                         0
% 7.82/1.48  parsing_time:                           0.009
% 7.82/1.48  unif_index_cands_time:                  0.
% 7.82/1.48  unif_index_add_time:                    0.
% 7.82/1.48  orderings_time:                         0.
% 7.82/1.48  out_proof_time:                         0.015
% 7.82/1.48  total_time:                             0.772
% 7.82/1.48  num_of_symbols:                         49
% 7.82/1.48  num_of_terms:                           28976
% 7.82/1.48  
% 7.82/1.48  ------ Preprocessing
% 7.82/1.48  
% 7.82/1.48  num_of_splits:                          0
% 7.82/1.48  num_of_split_atoms:                     0
% 7.82/1.48  num_of_reused_defs:                     0
% 7.82/1.48  num_eq_ax_congr_red:                    45
% 7.82/1.48  num_of_sem_filtered_clauses:            1
% 7.82/1.48  num_of_subtypes:                        3
% 7.82/1.48  monotx_restored_types:                  0
% 7.82/1.48  sat_num_of_epr_types:                   0
% 7.82/1.48  sat_num_of_non_cyclic_types:            0
% 7.82/1.48  sat_guarded_non_collapsed_types:        1
% 7.82/1.48  num_pure_diseq_elim:                    0
% 7.82/1.48  simp_replaced_by:                       0
% 7.82/1.48  res_preprocessed:                       111
% 7.82/1.48  prep_upred:                             0
% 7.82/1.48  prep_unflattend:                        21
% 7.82/1.48  smt_new_axioms:                         0
% 7.82/1.48  pred_elim_cands:                        2
% 7.82/1.48  pred_elim:                              6
% 7.82/1.48  pred_elim_cl:                           6
% 7.82/1.48  pred_elim_cycles:                       8
% 7.82/1.48  merged_defs:                            0
% 7.82/1.48  merged_defs_ncl:                        0
% 7.82/1.48  bin_hyper_res:                          0
% 7.82/1.48  prep_cycles:                            4
% 7.82/1.48  pred_elim_time:                         0.012
% 7.82/1.48  splitting_time:                         0.
% 7.82/1.48  sem_filter_time:                        0.
% 7.82/1.48  monotx_time:                            0.
% 7.82/1.48  subtype_inf_time:                       0.
% 7.82/1.48  
% 7.82/1.48  ------ Problem properties
% 7.82/1.48  
% 7.82/1.48  clauses:                                23
% 7.82/1.48  conjectures:                            3
% 7.82/1.48  epr:                                    0
% 7.82/1.48  horn:                                   17
% 7.82/1.48  ground:                                 3
% 7.82/1.48  unary:                                  3
% 7.82/1.48  binary:                                 0
% 7.82/1.48  lits:                                   107
% 7.82/1.48  lits_eq:                                13
% 7.82/1.48  fd_pure:                                0
% 7.82/1.48  fd_pseudo:                              0
% 7.82/1.48  fd_cond:                                0
% 7.82/1.48  fd_pseudo_cond:                         8
% 7.82/1.48  ac_symbols:                             0
% 7.82/1.48  
% 7.82/1.48  ------ Propositional Solver
% 7.82/1.48  
% 7.82/1.48  prop_solver_calls:                      31
% 7.82/1.48  prop_fast_solver_calls:                 2054
% 7.82/1.48  smt_solver_calls:                       0
% 7.82/1.48  smt_fast_solver_calls:                  0
% 7.82/1.48  prop_num_of_clauses:                    7297
% 7.82/1.48  prop_preprocess_simplified:             17393
% 7.82/1.48  prop_fo_subsumed:                       141
% 7.82/1.48  prop_solver_time:                       0.
% 7.82/1.48  smt_solver_time:                        0.
% 7.82/1.48  smt_fast_solver_time:                   0.
% 7.82/1.48  prop_fast_solver_time:                  0.
% 7.82/1.48  prop_unsat_core_time:                   0.
% 7.82/1.48  
% 7.82/1.48  ------ QBF
% 7.82/1.48  
% 7.82/1.48  qbf_q_res:                              0
% 7.82/1.48  qbf_num_tautologies:                    0
% 7.82/1.48  qbf_prep_cycles:                        0
% 7.82/1.48  
% 7.82/1.48  ------ BMC1
% 7.82/1.48  
% 7.82/1.48  bmc1_current_bound:                     -1
% 7.82/1.48  bmc1_last_solved_bound:                 -1
% 7.82/1.48  bmc1_unsat_core_size:                   -1
% 7.82/1.48  bmc1_unsat_core_parents_size:           -1
% 7.82/1.48  bmc1_merge_next_fun:                    0
% 7.82/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.82/1.48  
% 7.82/1.48  ------ Instantiation
% 7.82/1.48  
% 7.82/1.48  inst_num_of_clauses:                    1958
% 7.82/1.48  inst_num_in_passive:                    970
% 7.82/1.48  inst_num_in_active:                     826
% 7.82/1.48  inst_num_in_unprocessed:                161
% 7.82/1.48  inst_num_of_loops:                      1199
% 7.82/1.48  inst_num_of_learning_restarts:          0
% 7.82/1.48  inst_num_moves_active_passive:          369
% 7.82/1.48  inst_lit_activity:                      0
% 7.82/1.48  inst_lit_activity_moves:                1
% 7.82/1.48  inst_num_tautologies:                   0
% 7.82/1.48  inst_num_prop_implied:                  0
% 7.82/1.48  inst_num_existing_simplified:           0
% 7.82/1.48  inst_num_eq_res_simplified:             0
% 7.82/1.48  inst_num_child_elim:                    0
% 7.82/1.48  inst_num_of_dismatching_blockings:      2268
% 7.82/1.48  inst_num_of_non_proper_insts:           3633
% 7.82/1.48  inst_num_of_duplicates:                 0
% 7.82/1.48  inst_inst_num_from_inst_to_res:         0
% 7.82/1.48  inst_dismatching_checking_time:         0.
% 7.82/1.48  
% 7.82/1.48  ------ Resolution
% 7.82/1.48  
% 7.82/1.48  res_num_of_clauses:                     0
% 7.82/1.48  res_num_in_passive:                     0
% 7.82/1.48  res_num_in_active:                      0
% 7.82/1.48  res_num_of_loops:                       115
% 7.82/1.48  res_forward_subset_subsumed:            11
% 7.82/1.48  res_backward_subset_subsumed:           0
% 7.82/1.48  res_forward_subsumed:                   0
% 7.82/1.48  res_backward_subsumed:                  0
% 7.82/1.48  res_forward_subsumption_resolution:     0
% 7.82/1.48  res_backward_subsumption_resolution:    0
% 7.82/1.48  res_clause_to_clause_subsumption:       3126
% 7.82/1.48  res_orphan_elimination:                 0
% 7.82/1.48  res_tautology_del:                      60
% 7.82/1.48  res_num_eq_res_simplified:              0
% 7.82/1.48  res_num_sel_changes:                    0
% 7.82/1.48  res_moves_from_active_to_pass:          0
% 7.82/1.48  
% 7.82/1.48  ------ Superposition
% 7.82/1.48  
% 7.82/1.48  sup_time_total:                         0.
% 7.82/1.48  sup_time_generating:                    0.
% 7.82/1.48  sup_time_sim_full:                      0.
% 7.82/1.48  sup_time_sim_immed:                     0.
% 7.82/1.48  
% 7.82/1.48  sup_num_of_clauses:                     631
% 7.82/1.48  sup_num_in_active:                      196
% 7.82/1.48  sup_num_in_passive:                     435
% 7.82/1.48  sup_num_of_loops:                       238
% 7.82/1.48  sup_fw_superposition:                   526
% 7.82/1.48  sup_bw_superposition:                   219
% 7.82/1.48  sup_immediate_simplified:               145
% 7.82/1.48  sup_given_eliminated:                   0
% 7.82/1.48  comparisons_done:                       0
% 7.82/1.48  comparisons_avoided:                    0
% 7.82/1.48  
% 7.82/1.48  ------ Simplifications
% 7.82/1.48  
% 7.82/1.48  
% 7.82/1.48  sim_fw_subset_subsumed:                 15
% 7.82/1.48  sim_bw_subset_subsumed:                 14
% 7.82/1.48  sim_fw_subsumed:                        18
% 7.82/1.48  sim_bw_subsumed:                        0
% 7.82/1.48  sim_fw_subsumption_res:                 0
% 7.82/1.48  sim_bw_subsumption_res:                 0
% 7.82/1.48  sim_tautology_del:                      17
% 7.82/1.48  sim_eq_tautology_del:                   11
% 7.82/1.48  sim_eq_res_simp:                        0
% 7.82/1.48  sim_fw_demodulated:                     6
% 7.82/1.48  sim_bw_demodulated:                     41
% 7.82/1.48  sim_light_normalised:                   121
% 7.82/1.48  sim_joinable_taut:                      0
% 7.82/1.48  sim_joinable_simp:                      0
% 7.82/1.48  sim_ac_normalised:                      0
% 7.82/1.48  sim_smt_subsumption:                    0
% 7.82/1.48  
%------------------------------------------------------------------------------
