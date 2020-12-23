%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:03 EST 2020

% Result     : Theorem 15.67s
% Output     : CNFRefutation 15.67s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 998 expanded)
%              Number of clauses        :  115 ( 257 expanded)
%              Number of leaves         :   17 ( 313 expanded)
%              Depth                    :   20
%              Number of atoms          : 1058 (6511 expanded)
%              Number of equality atoms :  208 (1094 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   21 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,sK4)) != X1
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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

fof(f45,plain,
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

fof(f48,plain,
    ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_orders_2(sK2)
    & v2_lattice3(sK2)
    & v1_lattice3(sK2)
    & v5_orders_2(sK2)
    & v3_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f34,f47,f46,f45])).

fof(f76,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f48])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f75,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f72,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f74,plain,(
    v2_lattice3(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f73,plain,(
    v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f10,axiom,(
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

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f71,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f48])).

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
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

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
    inference(nnf_transformation,[],[f24])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
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

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f55,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

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
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

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
    inference(nnf_transformation,[],[f26])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f43,plain,(
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

fof(f44,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f42,f43])).

fof(f67,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f65,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f77,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f48])).

fof(f54,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f78,plain,(
    k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1209,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1592,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1209])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k12_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_25,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_941,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k12_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_25])).

cnf(c_942,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(k12_lattice3(sK2,X0,X1),u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ v2_lattice3(sK2) ),
    inference(unflattening,[status(thm)],[c_941])).

cnf(c_28,negated_conjecture,
    ( v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_26,negated_conjecture,
    ( v2_lattice3(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_946,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(k12_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_942,c_28,c_26])).

cnf(c_1190,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | m1_subset_1(k12_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_946])).

cnf(c_1611,plain,
    ( m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k12_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1190])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_27,negated_conjecture,
    ( v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_615,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_616,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k10_lattice3(sK2,X0,X1) = k13_lattice3(sK2,X0,X1) ),
    inference(unflattening,[status(thm)],[c_615])).

cnf(c_620,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k10_lattice3(sK2,X0,X1) = k13_lattice3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_616,c_28,c_25])).

cnf(c_1200,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | k10_lattice3(sK2,X0_46,X1_46) = k13_lattice3(sK2,X0_46,X1_46) ),
    inference(subtyping,[status(esa)],[c_620])).

cnf(c_1601,plain,
    ( k10_lattice3(sK2,X0_46,X1_46) = k13_lattice3(sK2,X0_46,X1_46)
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1200])).

cnf(c_3941,plain,
    ( k10_lattice3(sK2,k12_lattice3(sK2,X0_46,X1_46),X2_46) = k13_lattice3(sK2,k12_lattice3(sK2,X0_46,X1_46),X2_46)
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_46,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1611,c_1601])).

cnf(c_32756,plain,
    ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,X0_46),X1_46) = k13_lattice3(sK2,k12_lattice3(sK2,sK3,X0_46),X1_46)
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1592,c_3941])).

cnf(c_37005,plain,
    ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK3),X0_46) = k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK3),X0_46)
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1592,c_32756])).

cnf(c_37879,plain,
    ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK3),sK3) = k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK3),sK3) ),
    inference(superposition,[status(thm)],[c_1592,c_37005])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | k13_lattice3(X1,k12_lattice3(X1,X2,X0),X0) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_29,negated_conjecture,
    ( v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_385,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | k13_lattice3(X1,k12_lattice3(X1,X2,X0),X0) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_29])).

cnf(c_386,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ v2_lattice3(sK2)
    | ~ l1_orders_2(sK2)
    | ~ v1_lattice3(sK2)
    | k13_lattice3(sK2,k12_lattice3(sK2,X0,X1),X1) = X1 ),
    inference(unflattening,[status(thm)],[c_385])).

cnf(c_390,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k13_lattice3(sK2,k12_lattice3(sK2,X0,X1),X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_386,c_28,c_27,c_26,c_25])).

cnf(c_1208,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | k13_lattice3(sK2,k12_lattice3(sK2,X0_46,X1_46),X1_46) = X1_46 ),
    inference(subtyping,[status(esa)],[c_390])).

cnf(c_1593,plain,
    ( k13_lattice3(sK2,k12_lattice3(sK2,X0_46,X1_46),X1_46) = X1_46
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1208])).

cnf(c_1883,plain,
    ( k13_lattice3(sK2,k12_lattice3(sK2,sK3,X0_46),X0_46) = X0_46
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1592,c_1593])).

cnf(c_2008,plain,
    ( k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK3),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_1592,c_1883])).

cnf(c_37925,plain,
    ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK3),sK3) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_37879,c_2008])).

cnf(c_10,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_216,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_0])).

cnf(c_217,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0) ),
    inference(renaming,[status(thm)],[c_216])).

cnf(c_571,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_217,c_27])).

cnf(c_572,plain,
    ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X1,X0),u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_571])).

cnf(c_576,plain,
    ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X1,X0),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_572,c_28,c_25])).

cnf(c_577,plain,
    ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X1,X0),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_576])).

cnf(c_1202,plain,
    ( r1_orders_2(sK2,X0_46,k10_lattice3(sK2,X1_46,X0_46))
    | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X1_46,X0_46),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_577])).

cnf(c_1599,plain,
    ( r1_orders_2(sK2,X0_46,k10_lattice3(sK2,X1_46,X0_46)) = iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k10_lattice3(sK2,X1_46,X0_46),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1202])).

cnf(c_38614,plain,
    ( r1_orders_2(sK2,sK3,k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK3),sK3)) = iProver_top
    | m1_subset_1(k12_lattice3(sK2,sK3,sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_37925,c_1599])).

cnf(c_38626,plain,
    ( r1_orders_2(sK2,sK3,sK3) = iProver_top
    | m1_subset_1(k12_lattice3(sK2,sK3,sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_38614,c_37925])).

cnf(c_12,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK1(X0,X3,X2,X1),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1,plain,
    ( ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_202,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_orders_2(X0,sK1(X0,X3,X2,X1),X1)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X1,X2)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_1])).

cnf(c_203,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK1(X0,X2,X3,X1),X1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X2,X3) = X1 ),
    inference(renaming,[status(thm)],[c_202])).

cnf(c_715,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK1(X0,X3,X2,X1),X1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | k11_lattice3(X0,X3,X2) = X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_203,c_25])).

cnf(c_716,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | ~ r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ v2_lattice3(sK2)
    | k11_lattice3(sK2,X2,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_715])).

cnf(c_720,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | ~ r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | k11_lattice3(sK2,X2,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_716,c_28,c_26])).

cnf(c_721,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | ~ r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X0)
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k11_lattice3(sK2,X2,X1) = X0 ),
    inference(renaming,[status(thm)],[c_720])).

cnf(c_1198,plain,
    ( ~ r1_orders_2(sK2,X0_46,X1_46)
    | ~ r1_orders_2(sK2,X0_46,X2_46)
    | ~ r1_orders_2(sK2,sK1(sK2,X2_46,X1_46,X0_46),X0_46)
    | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X2_46,u1_struct_0(sK2))
    | k11_lattice3(sK2,X2_46,X1_46) = X0_46 ),
    inference(subtyping,[status(esa)],[c_721])).

cnf(c_9517,plain,
    ( ~ r1_orders_2(sK2,X0_46,k13_lattice3(sK2,sK3,sK4))
    | ~ r1_orders_2(sK2,X0_46,sK3)
    | ~ r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_46),X0_46)
    | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46 ),
    inference(instantiation,[status(thm)],[c_1198])).

cnf(c_9533,plain,
    ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46
    | r1_orders_2(sK2,X0_46,k13_lattice3(sK2,sK3,sK4)) != iProver_top
    | r1_orders_2(sK2,X0_46,sK3) != iProver_top
    | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_46),X0_46) != iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9517])).

cnf(c_9535,plain,
    ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
    | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),sK3),sK3) != iProver_top
    | r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != iProver_top
    | r1_orders_2(sK2,sK3,sK3) != iProver_top
    | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9533])).

cnf(c_14,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK1(X0,X3,X2,X1),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_190,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,sK1(X0,X3,X2,X1),X3)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X1,X2)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_1])).

cnf(c_191,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK1(X0,X2,X3,X1),X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X2,X3) = X1 ),
    inference(renaming,[status(thm)],[c_190])).

cnf(c_781,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK1(X0,X3,X2,X1),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | k11_lattice3(X0,X3,X2) = X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_191,c_25])).

cnf(c_782,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ v2_lattice3(sK2)
    | k11_lattice3(sK2,X2,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_781])).

cnf(c_784,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | k11_lattice3(sK2,X2,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_782,c_28,c_26])).

cnf(c_785,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k11_lattice3(sK2,X2,X1) = X0 ),
    inference(renaming,[status(thm)],[c_784])).

cnf(c_1196,plain,
    ( ~ r1_orders_2(sK2,X0_46,X1_46)
    | ~ r1_orders_2(sK2,X0_46,X2_46)
    | r1_orders_2(sK2,sK1(sK2,X2_46,X1_46,X0_46),X2_46)
    | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X2_46,u1_struct_0(sK2))
    | k11_lattice3(sK2,X2_46,X1_46) = X0_46 ),
    inference(subtyping,[status(esa)],[c_785])).

cnf(c_9519,plain,
    ( ~ r1_orders_2(sK2,X0_46,k13_lattice3(sK2,sK3,sK4))
    | ~ r1_orders_2(sK2,X0_46,sK3)
    | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_46),sK3)
    | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46 ),
    inference(instantiation,[status(thm)],[c_1196])).

cnf(c_9525,plain,
    ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46
    | r1_orders_2(sK2,X0_46,k13_lattice3(sK2,sK3,sK4)) != iProver_top
    | r1_orders_2(sK2,X0_46,sK3) != iProver_top
    | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_46),sK3) = iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9519])).

cnf(c_9527,plain,
    ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
    | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),sK3),sK3) = iProver_top
    | r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != iProver_top
    | r1_orders_2(sK2,sK3,sK3) != iProver_top
    | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9525])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1210,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1591,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1210])).

cnf(c_2242,plain,
    ( k10_lattice3(sK2,sK3,X0_46) = k13_lattice3(sK2,sK3,X0_46)
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1592,c_1601])).

cnf(c_2360,plain,
    ( k10_lattice3(sK2,sK3,sK4) = k13_lattice3(sK2,sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1591,c_2242])).

cnf(c_11,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_209,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_0])).

cnf(c_210,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0) ),
    inference(renaming,[status(thm)],[c_209])).

cnf(c_595,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_210,c_27])).

cnf(c_596,plain,
    ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_595])).

cnf(c_598,plain,
    ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_596,c_28,c_25])).

cnf(c_599,plain,
    ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_598])).

cnf(c_1201,plain,
    ( r1_orders_2(sK2,X0_46,k10_lattice3(sK2,X0_46,X1_46))
    | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_599])).

cnf(c_1600,plain,
    ( r1_orders_2(sK2,X0_46,k10_lattice3(sK2,X0_46,X1_46)) = iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k10_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1201])).

cnf(c_4989,plain,
    ( r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK4)) = iProver_top
    | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2360,c_1600])).

cnf(c_4994,plain,
    ( r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = iProver_top
    | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4989,c_2360])).

cnf(c_1214,plain,
    ( X0_46 != X1_46
    | X2_46 != X1_46
    | X2_46 = X0_46 ),
    theory(equality)).

cnf(c_2331,plain,
    ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != X0_46
    | sK3 != X0_46
    | sK3 = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1214])).

cnf(c_2332,plain,
    ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3
    | sK3 = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2331])).

cnf(c_1896,plain,
    ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != X0_46
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
    | sK3 != X0_46 ),
    inference(instantiation,[status(thm)],[c_1214])).

cnf(c_2327,plain,
    ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
    | sK3 != k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1896])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_920,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_25])).

cnf(c_921,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ v2_lattice3(sK2)
    | k11_lattice3(sK2,X0,X1) = k12_lattice3(sK2,X0,X1) ),
    inference(unflattening,[status(thm)],[c_920])).

cnf(c_925,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k11_lattice3(sK2,X0,X1) = k12_lattice3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_921,c_28,c_26])).

cnf(c_1191,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | k11_lattice3(sK2,X0_46,X1_46) = k12_lattice3(sK2,X0_46,X1_46) ),
    inference(subtyping,[status(esa)],[c_925])).

cnf(c_2276,plain,
    ( ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1191])).

cnf(c_1925,plain,
    ( X0_46 != X1_46
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != X1_46
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46 ),
    inference(instantiation,[status(thm)],[c_1214])).

cnf(c_2020,plain,
    ( X0_46 != k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1925])).

cnf(c_2275,plain,
    ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2020])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k13_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_636,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k13_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_27])).

cnf(c_637,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(k13_lattice3(sK2,X0,X1),u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_636])).

cnf(c_641,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(k13_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_637,c_28,c_25])).

cnf(c_1199,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | m1_subset_1(k13_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_641])).

cnf(c_1998,plain,
    ( m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1199])).

cnf(c_1999,plain,
    ( m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1998])).

cnf(c_1213,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_1924,plain,
    ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1213])).

cnf(c_1273,plain,
    ( m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k12_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1190])).

cnf(c_1275,plain,
    ( m1_subset_1(k12_lattice3(sK2,sK3,sK3),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1273])).

cnf(c_22,negated_conjecture,
    ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1211,negated_conjecture,
    ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1224,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1213])).

cnf(c_36,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_35,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_38626,c_9535,c_9527,c_4994,c_2332,c_2327,c_2276,c_2275,c_1999,c_1998,c_1924,c_1275,c_1211,c_1224,c_36,c_23,c_35,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:48:08 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.67/2.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.67/2.50  
% 15.67/2.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.67/2.50  
% 15.67/2.50  ------  iProver source info
% 15.67/2.50  
% 15.67/2.50  git: date: 2020-06-30 10:37:57 +0100
% 15.67/2.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.67/2.50  git: non_committed_changes: false
% 15.67/2.50  git: last_make_outside_of_git: false
% 15.67/2.50  
% 15.67/2.50  ------ 
% 15.67/2.50  
% 15.67/2.50  ------ Input Options
% 15.67/2.50  
% 15.67/2.50  --out_options                           all
% 15.67/2.50  --tptp_safe_out                         true
% 15.67/2.50  --problem_path                          ""
% 15.67/2.50  --include_path                          ""
% 15.67/2.50  --clausifier                            res/vclausify_rel
% 15.67/2.50  --clausifier_options                    --mode clausify
% 15.67/2.50  --stdin                                 false
% 15.67/2.50  --stats_out                             all
% 15.67/2.50  
% 15.67/2.50  ------ General Options
% 15.67/2.50  
% 15.67/2.50  --fof                                   false
% 15.67/2.50  --time_out_real                         305.
% 15.67/2.50  --time_out_virtual                      -1.
% 15.67/2.50  --symbol_type_check                     false
% 15.67/2.50  --clausify_out                          false
% 15.67/2.50  --sig_cnt_out                           false
% 15.67/2.50  --trig_cnt_out                          false
% 15.67/2.50  --trig_cnt_out_tolerance                1.
% 15.67/2.50  --trig_cnt_out_sk_spl                   false
% 15.67/2.50  --abstr_cl_out                          false
% 15.67/2.50  
% 15.67/2.50  ------ Global Options
% 15.67/2.50  
% 15.67/2.50  --schedule                              default
% 15.67/2.50  --add_important_lit                     false
% 15.67/2.50  --prop_solver_per_cl                    1000
% 15.67/2.50  --min_unsat_core                        false
% 15.67/2.50  --soft_assumptions                      false
% 15.67/2.50  --soft_lemma_size                       3
% 15.67/2.50  --prop_impl_unit_size                   0
% 15.67/2.50  --prop_impl_unit                        []
% 15.67/2.50  --share_sel_clauses                     true
% 15.67/2.50  --reset_solvers                         false
% 15.67/2.50  --bc_imp_inh                            [conj_cone]
% 15.67/2.50  --conj_cone_tolerance                   3.
% 15.67/2.50  --extra_neg_conj                        none
% 15.67/2.50  --large_theory_mode                     true
% 15.67/2.50  --prolific_symb_bound                   200
% 15.67/2.50  --lt_threshold                          2000
% 15.67/2.50  --clause_weak_htbl                      true
% 15.67/2.50  --gc_record_bc_elim                     false
% 15.67/2.50  
% 15.67/2.50  ------ Preprocessing Options
% 15.67/2.50  
% 15.67/2.50  --preprocessing_flag                    true
% 15.67/2.50  --time_out_prep_mult                    0.1
% 15.67/2.50  --splitting_mode                        input
% 15.67/2.50  --splitting_grd                         true
% 15.67/2.50  --splitting_cvd                         false
% 15.67/2.50  --splitting_cvd_svl                     false
% 15.67/2.50  --splitting_nvd                         32
% 15.67/2.50  --sub_typing                            true
% 15.67/2.50  --prep_gs_sim                           true
% 15.67/2.50  --prep_unflatten                        true
% 15.67/2.50  --prep_res_sim                          true
% 15.67/2.50  --prep_upred                            true
% 15.67/2.50  --prep_sem_filter                       exhaustive
% 15.67/2.50  --prep_sem_filter_out                   false
% 15.67/2.50  --pred_elim                             true
% 15.67/2.50  --res_sim_input                         true
% 15.67/2.50  --eq_ax_congr_red                       true
% 15.67/2.50  --pure_diseq_elim                       true
% 15.67/2.50  --brand_transform                       false
% 15.67/2.50  --non_eq_to_eq                          false
% 15.67/2.50  --prep_def_merge                        true
% 15.67/2.50  --prep_def_merge_prop_impl              false
% 15.67/2.50  --prep_def_merge_mbd                    true
% 15.67/2.50  --prep_def_merge_tr_red                 false
% 15.67/2.50  --prep_def_merge_tr_cl                  false
% 15.67/2.50  --smt_preprocessing                     true
% 15.67/2.50  --smt_ac_axioms                         fast
% 15.67/2.50  --preprocessed_out                      false
% 15.67/2.50  --preprocessed_stats                    false
% 15.67/2.50  
% 15.67/2.50  ------ Abstraction refinement Options
% 15.67/2.50  
% 15.67/2.50  --abstr_ref                             []
% 15.67/2.50  --abstr_ref_prep                        false
% 15.67/2.50  --abstr_ref_until_sat                   false
% 15.67/2.50  --abstr_ref_sig_restrict                funpre
% 15.67/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 15.67/2.50  --abstr_ref_under                       []
% 15.67/2.50  
% 15.67/2.50  ------ SAT Options
% 15.67/2.50  
% 15.67/2.50  --sat_mode                              false
% 15.67/2.50  --sat_fm_restart_options                ""
% 15.67/2.50  --sat_gr_def                            false
% 15.67/2.50  --sat_epr_types                         true
% 15.67/2.50  --sat_non_cyclic_types                  false
% 15.67/2.50  --sat_finite_models                     false
% 15.67/2.50  --sat_fm_lemmas                         false
% 15.67/2.50  --sat_fm_prep                           false
% 15.67/2.50  --sat_fm_uc_incr                        true
% 15.67/2.50  --sat_out_model                         small
% 15.67/2.50  --sat_out_clauses                       false
% 15.67/2.50  
% 15.67/2.50  ------ QBF Options
% 15.67/2.50  
% 15.67/2.50  --qbf_mode                              false
% 15.67/2.50  --qbf_elim_univ                         false
% 15.67/2.50  --qbf_dom_inst                          none
% 15.67/2.50  --qbf_dom_pre_inst                      false
% 15.67/2.50  --qbf_sk_in                             false
% 15.67/2.50  --qbf_pred_elim                         true
% 15.67/2.50  --qbf_split                             512
% 15.67/2.50  
% 15.67/2.50  ------ BMC1 Options
% 15.67/2.50  
% 15.67/2.50  --bmc1_incremental                      false
% 15.67/2.50  --bmc1_axioms                           reachable_all
% 15.67/2.50  --bmc1_min_bound                        0
% 15.67/2.50  --bmc1_max_bound                        -1
% 15.67/2.50  --bmc1_max_bound_default                -1
% 15.67/2.50  --bmc1_symbol_reachability              true
% 15.67/2.50  --bmc1_property_lemmas                  false
% 15.67/2.50  --bmc1_k_induction                      false
% 15.67/2.50  --bmc1_non_equiv_states                 false
% 15.67/2.50  --bmc1_deadlock                         false
% 15.67/2.50  --bmc1_ucm                              false
% 15.67/2.50  --bmc1_add_unsat_core                   none
% 15.67/2.50  --bmc1_unsat_core_children              false
% 15.67/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 15.67/2.50  --bmc1_out_stat                         full
% 15.67/2.50  --bmc1_ground_init                      false
% 15.67/2.50  --bmc1_pre_inst_next_state              false
% 15.67/2.50  --bmc1_pre_inst_state                   false
% 15.67/2.50  --bmc1_pre_inst_reach_state             false
% 15.67/2.50  --bmc1_out_unsat_core                   false
% 15.67/2.50  --bmc1_aig_witness_out                  false
% 15.67/2.50  --bmc1_verbose                          false
% 15.67/2.50  --bmc1_dump_clauses_tptp                false
% 15.67/2.50  --bmc1_dump_unsat_core_tptp             false
% 15.67/2.50  --bmc1_dump_file                        -
% 15.67/2.50  --bmc1_ucm_expand_uc_limit              128
% 15.67/2.50  --bmc1_ucm_n_expand_iterations          6
% 15.67/2.50  --bmc1_ucm_extend_mode                  1
% 15.67/2.50  --bmc1_ucm_init_mode                    2
% 15.67/2.50  --bmc1_ucm_cone_mode                    none
% 15.67/2.50  --bmc1_ucm_reduced_relation_type        0
% 15.67/2.50  --bmc1_ucm_relax_model                  4
% 15.67/2.50  --bmc1_ucm_full_tr_after_sat            true
% 15.67/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 15.67/2.50  --bmc1_ucm_layered_model                none
% 15.67/2.50  --bmc1_ucm_max_lemma_size               10
% 15.67/2.50  
% 15.67/2.50  ------ AIG Options
% 15.67/2.50  
% 15.67/2.50  --aig_mode                              false
% 15.67/2.50  
% 15.67/2.50  ------ Instantiation Options
% 15.67/2.50  
% 15.67/2.50  --instantiation_flag                    true
% 15.67/2.50  --inst_sos_flag                         false
% 15.67/2.50  --inst_sos_phase                        true
% 15.67/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.67/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.67/2.50  --inst_lit_sel_side                     num_symb
% 15.67/2.50  --inst_solver_per_active                1400
% 15.67/2.50  --inst_solver_calls_frac                1.
% 15.67/2.50  --inst_passive_queue_type               priority_queues
% 15.67/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.67/2.50  --inst_passive_queues_freq              [25;2]
% 15.67/2.50  --inst_dismatching                      true
% 15.67/2.50  --inst_eager_unprocessed_to_passive     true
% 15.67/2.50  --inst_prop_sim_given                   true
% 15.67/2.50  --inst_prop_sim_new                     false
% 15.67/2.50  --inst_subs_new                         false
% 15.67/2.50  --inst_eq_res_simp                      false
% 15.67/2.50  --inst_subs_given                       false
% 15.67/2.50  --inst_orphan_elimination               true
% 15.67/2.50  --inst_learning_loop_flag               true
% 15.67/2.50  --inst_learning_start                   3000
% 15.67/2.50  --inst_learning_factor                  2
% 15.67/2.50  --inst_start_prop_sim_after_learn       3
% 15.67/2.50  --inst_sel_renew                        solver
% 15.67/2.50  --inst_lit_activity_flag                true
% 15.67/2.50  --inst_restr_to_given                   false
% 15.67/2.50  --inst_activity_threshold               500
% 15.67/2.50  --inst_out_proof                        true
% 15.67/2.50  
% 15.67/2.50  ------ Resolution Options
% 15.67/2.50  
% 15.67/2.50  --resolution_flag                       true
% 15.67/2.50  --res_lit_sel                           adaptive
% 15.67/2.50  --res_lit_sel_side                      none
% 15.67/2.50  --res_ordering                          kbo
% 15.67/2.50  --res_to_prop_solver                    active
% 15.67/2.50  --res_prop_simpl_new                    false
% 15.67/2.50  --res_prop_simpl_given                  true
% 15.67/2.50  --res_passive_queue_type                priority_queues
% 15.67/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.67/2.50  --res_passive_queues_freq               [15;5]
% 15.67/2.50  --res_forward_subs                      full
% 15.67/2.50  --res_backward_subs                     full
% 15.67/2.50  --res_forward_subs_resolution           true
% 15.67/2.50  --res_backward_subs_resolution          true
% 15.67/2.50  --res_orphan_elimination                true
% 15.67/2.50  --res_time_limit                        2.
% 15.67/2.50  --res_out_proof                         true
% 15.67/2.50  
% 15.67/2.50  ------ Superposition Options
% 15.67/2.50  
% 15.67/2.50  --superposition_flag                    true
% 15.67/2.50  --sup_passive_queue_type                priority_queues
% 15.67/2.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.67/2.50  --sup_passive_queues_freq               [8;1;4]
% 15.67/2.50  --demod_completeness_check              fast
% 15.67/2.50  --demod_use_ground                      true
% 15.67/2.50  --sup_to_prop_solver                    passive
% 15.67/2.50  --sup_prop_simpl_new                    true
% 15.67/2.50  --sup_prop_simpl_given                  true
% 15.67/2.50  --sup_fun_splitting                     false
% 15.67/2.50  --sup_smt_interval                      50000
% 15.67/2.50  
% 15.67/2.50  ------ Superposition Simplification Setup
% 15.67/2.50  
% 15.67/2.50  --sup_indices_passive                   []
% 15.67/2.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.67/2.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.67/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.67/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 15.67/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.67/2.50  --sup_full_bw                           [BwDemod]
% 15.67/2.50  --sup_immed_triv                        [TrivRules]
% 15.67/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.67/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.67/2.50  --sup_immed_bw_main                     []
% 15.67/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.67/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 15.67/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.67/2.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.67/2.50  
% 15.67/2.50  ------ Combination Options
% 15.67/2.50  
% 15.67/2.50  --comb_res_mult                         3
% 15.67/2.50  --comb_sup_mult                         2
% 15.67/2.50  --comb_inst_mult                        10
% 15.67/2.50  
% 15.67/2.50  ------ Debug Options
% 15.67/2.50  
% 15.67/2.50  --dbg_backtrace                         false
% 15.67/2.50  --dbg_dump_prop_clauses                 false
% 15.67/2.50  --dbg_dump_prop_clauses_file            -
% 15.67/2.50  --dbg_out_stat                          false
% 15.67/2.50  ------ Parsing...
% 15.67/2.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.67/2.50  
% 15.67/2.50  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 15.67/2.50  
% 15.67/2.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.67/2.50  
% 15.67/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.67/2.50  ------ Proving...
% 15.67/2.50  ------ Problem Properties 
% 15.67/2.50  
% 15.67/2.50  
% 15.67/2.50  clauses                                 23
% 15.67/2.50  conjectures                             3
% 15.67/2.50  EPR                                     0
% 15.67/2.50  Horn                                    17
% 15.67/2.50  unary                                   3
% 15.67/2.50  binary                                  0
% 15.67/2.50  lits                                    107
% 15.67/2.50  lits eq                                 13
% 15.67/2.50  fd_pure                                 0
% 15.67/2.50  fd_pseudo                               0
% 15.67/2.50  fd_cond                                 0
% 15.67/2.50  fd_pseudo_cond                          8
% 15.67/2.50  AC symbols                              0
% 15.67/2.50  
% 15.67/2.50  ------ Schedule dynamic 5 is on 
% 15.67/2.50  
% 15.67/2.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.67/2.50  
% 15.67/2.50  
% 15.67/2.50  ------ 
% 15.67/2.50  Current options:
% 15.67/2.50  ------ 
% 15.67/2.50  
% 15.67/2.50  ------ Input Options
% 15.67/2.50  
% 15.67/2.50  --out_options                           all
% 15.67/2.50  --tptp_safe_out                         true
% 15.67/2.50  --problem_path                          ""
% 15.67/2.50  --include_path                          ""
% 15.67/2.50  --clausifier                            res/vclausify_rel
% 15.67/2.50  --clausifier_options                    --mode clausify
% 15.67/2.50  --stdin                                 false
% 15.67/2.50  --stats_out                             all
% 15.67/2.50  
% 15.67/2.50  ------ General Options
% 15.67/2.50  
% 15.67/2.50  --fof                                   false
% 15.67/2.50  --time_out_real                         305.
% 15.67/2.50  --time_out_virtual                      -1.
% 15.67/2.50  --symbol_type_check                     false
% 15.67/2.50  --clausify_out                          false
% 15.67/2.50  --sig_cnt_out                           false
% 15.67/2.50  --trig_cnt_out                          false
% 15.67/2.50  --trig_cnt_out_tolerance                1.
% 15.67/2.50  --trig_cnt_out_sk_spl                   false
% 15.67/2.50  --abstr_cl_out                          false
% 15.67/2.50  
% 15.67/2.50  ------ Global Options
% 15.67/2.50  
% 15.67/2.50  --schedule                              default
% 15.67/2.50  --add_important_lit                     false
% 15.67/2.50  --prop_solver_per_cl                    1000
% 15.67/2.50  --min_unsat_core                        false
% 15.67/2.50  --soft_assumptions                      false
% 15.67/2.50  --soft_lemma_size                       3
% 15.67/2.50  --prop_impl_unit_size                   0
% 15.67/2.50  --prop_impl_unit                        []
% 15.67/2.50  --share_sel_clauses                     true
% 15.67/2.50  --reset_solvers                         false
% 15.67/2.50  --bc_imp_inh                            [conj_cone]
% 15.67/2.50  --conj_cone_tolerance                   3.
% 15.67/2.50  --extra_neg_conj                        none
% 15.67/2.50  --large_theory_mode                     true
% 15.67/2.50  --prolific_symb_bound                   200
% 15.67/2.50  --lt_threshold                          2000
% 15.67/2.50  --clause_weak_htbl                      true
% 15.67/2.50  --gc_record_bc_elim                     false
% 15.67/2.50  
% 15.67/2.50  ------ Preprocessing Options
% 15.67/2.50  
% 15.67/2.50  --preprocessing_flag                    true
% 15.67/2.50  --time_out_prep_mult                    0.1
% 15.67/2.50  --splitting_mode                        input
% 15.67/2.50  --splitting_grd                         true
% 15.67/2.50  --splitting_cvd                         false
% 15.67/2.50  --splitting_cvd_svl                     false
% 15.67/2.50  --splitting_nvd                         32
% 15.67/2.50  --sub_typing                            true
% 15.67/2.50  --prep_gs_sim                           true
% 15.67/2.50  --prep_unflatten                        true
% 15.67/2.50  --prep_res_sim                          true
% 15.67/2.50  --prep_upred                            true
% 15.67/2.50  --prep_sem_filter                       exhaustive
% 15.67/2.50  --prep_sem_filter_out                   false
% 15.67/2.50  --pred_elim                             true
% 15.67/2.50  --res_sim_input                         true
% 15.67/2.50  --eq_ax_congr_red                       true
% 15.67/2.50  --pure_diseq_elim                       true
% 15.67/2.50  --brand_transform                       false
% 15.67/2.50  --non_eq_to_eq                          false
% 15.67/2.50  --prep_def_merge                        true
% 15.67/2.50  --prep_def_merge_prop_impl              false
% 15.67/2.50  --prep_def_merge_mbd                    true
% 15.67/2.50  --prep_def_merge_tr_red                 false
% 15.67/2.50  --prep_def_merge_tr_cl                  false
% 15.67/2.50  --smt_preprocessing                     true
% 15.67/2.50  --smt_ac_axioms                         fast
% 15.67/2.50  --preprocessed_out                      false
% 15.67/2.50  --preprocessed_stats                    false
% 15.67/2.50  
% 15.67/2.50  ------ Abstraction refinement Options
% 15.67/2.50  
% 15.67/2.50  --abstr_ref                             []
% 15.67/2.50  --abstr_ref_prep                        false
% 15.67/2.50  --abstr_ref_until_sat                   false
% 15.67/2.50  --abstr_ref_sig_restrict                funpre
% 15.67/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 15.67/2.50  --abstr_ref_under                       []
% 15.67/2.50  
% 15.67/2.50  ------ SAT Options
% 15.67/2.50  
% 15.67/2.50  --sat_mode                              false
% 15.67/2.50  --sat_fm_restart_options                ""
% 15.67/2.50  --sat_gr_def                            false
% 15.67/2.50  --sat_epr_types                         true
% 15.67/2.50  --sat_non_cyclic_types                  false
% 15.67/2.50  --sat_finite_models                     false
% 15.67/2.50  --sat_fm_lemmas                         false
% 15.67/2.50  --sat_fm_prep                           false
% 15.67/2.50  --sat_fm_uc_incr                        true
% 15.67/2.50  --sat_out_model                         small
% 15.67/2.50  --sat_out_clauses                       false
% 15.67/2.50  
% 15.67/2.50  ------ QBF Options
% 15.67/2.50  
% 15.67/2.50  --qbf_mode                              false
% 15.67/2.50  --qbf_elim_univ                         false
% 15.67/2.50  --qbf_dom_inst                          none
% 15.67/2.50  --qbf_dom_pre_inst                      false
% 15.67/2.50  --qbf_sk_in                             false
% 15.67/2.50  --qbf_pred_elim                         true
% 15.67/2.50  --qbf_split                             512
% 15.67/2.50  
% 15.67/2.50  ------ BMC1 Options
% 15.67/2.50  
% 15.67/2.50  --bmc1_incremental                      false
% 15.67/2.50  --bmc1_axioms                           reachable_all
% 15.67/2.50  --bmc1_min_bound                        0
% 15.67/2.50  --bmc1_max_bound                        -1
% 15.67/2.50  --bmc1_max_bound_default                -1
% 15.67/2.50  --bmc1_symbol_reachability              true
% 15.67/2.50  --bmc1_property_lemmas                  false
% 15.67/2.50  --bmc1_k_induction                      false
% 15.67/2.50  --bmc1_non_equiv_states                 false
% 15.67/2.50  --bmc1_deadlock                         false
% 15.67/2.50  --bmc1_ucm                              false
% 15.67/2.50  --bmc1_add_unsat_core                   none
% 15.67/2.50  --bmc1_unsat_core_children              false
% 15.67/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 15.67/2.50  --bmc1_out_stat                         full
% 15.67/2.50  --bmc1_ground_init                      false
% 15.67/2.50  --bmc1_pre_inst_next_state              false
% 15.67/2.50  --bmc1_pre_inst_state                   false
% 15.67/2.50  --bmc1_pre_inst_reach_state             false
% 15.67/2.50  --bmc1_out_unsat_core                   false
% 15.67/2.50  --bmc1_aig_witness_out                  false
% 15.67/2.50  --bmc1_verbose                          false
% 15.67/2.50  --bmc1_dump_clauses_tptp                false
% 15.67/2.50  --bmc1_dump_unsat_core_tptp             false
% 15.67/2.50  --bmc1_dump_file                        -
% 15.67/2.50  --bmc1_ucm_expand_uc_limit              128
% 15.67/2.50  --bmc1_ucm_n_expand_iterations          6
% 15.67/2.50  --bmc1_ucm_extend_mode                  1
% 15.67/2.50  --bmc1_ucm_init_mode                    2
% 15.67/2.50  --bmc1_ucm_cone_mode                    none
% 15.67/2.50  --bmc1_ucm_reduced_relation_type        0
% 15.67/2.50  --bmc1_ucm_relax_model                  4
% 15.67/2.50  --bmc1_ucm_full_tr_after_sat            true
% 15.67/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 15.67/2.50  --bmc1_ucm_layered_model                none
% 15.67/2.50  --bmc1_ucm_max_lemma_size               10
% 15.67/2.50  
% 15.67/2.50  ------ AIG Options
% 15.67/2.50  
% 15.67/2.50  --aig_mode                              false
% 15.67/2.50  
% 15.67/2.50  ------ Instantiation Options
% 15.67/2.50  
% 15.67/2.50  --instantiation_flag                    true
% 15.67/2.50  --inst_sos_flag                         false
% 15.67/2.50  --inst_sos_phase                        true
% 15.67/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.67/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.67/2.50  --inst_lit_sel_side                     none
% 15.67/2.50  --inst_solver_per_active                1400
% 15.67/2.50  --inst_solver_calls_frac                1.
% 15.67/2.50  --inst_passive_queue_type               priority_queues
% 15.67/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.67/2.50  --inst_passive_queues_freq              [25;2]
% 15.67/2.50  --inst_dismatching                      true
% 15.67/2.50  --inst_eager_unprocessed_to_passive     true
% 15.67/2.50  --inst_prop_sim_given                   true
% 15.67/2.50  --inst_prop_sim_new                     false
% 15.67/2.50  --inst_subs_new                         false
% 15.67/2.50  --inst_eq_res_simp                      false
% 15.67/2.50  --inst_subs_given                       false
% 15.67/2.50  --inst_orphan_elimination               true
% 15.67/2.50  --inst_learning_loop_flag               true
% 15.67/2.50  --inst_learning_start                   3000
% 15.67/2.50  --inst_learning_factor                  2
% 15.67/2.50  --inst_start_prop_sim_after_learn       3
% 15.67/2.50  --inst_sel_renew                        solver
% 15.67/2.50  --inst_lit_activity_flag                true
% 15.67/2.50  --inst_restr_to_given                   false
% 15.67/2.50  --inst_activity_threshold               500
% 15.67/2.50  --inst_out_proof                        true
% 15.67/2.50  
% 15.67/2.50  ------ Resolution Options
% 15.67/2.50  
% 15.67/2.50  --resolution_flag                       false
% 15.67/2.50  --res_lit_sel                           adaptive
% 15.67/2.50  --res_lit_sel_side                      none
% 15.67/2.50  --res_ordering                          kbo
% 15.67/2.50  --res_to_prop_solver                    active
% 15.67/2.50  --res_prop_simpl_new                    false
% 15.67/2.50  --res_prop_simpl_given                  true
% 15.67/2.50  --res_passive_queue_type                priority_queues
% 15.67/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.67/2.50  --res_passive_queues_freq               [15;5]
% 15.67/2.50  --res_forward_subs                      full
% 15.67/2.50  --res_backward_subs                     full
% 15.67/2.50  --res_forward_subs_resolution           true
% 15.67/2.50  --res_backward_subs_resolution          true
% 15.67/2.50  --res_orphan_elimination                true
% 15.67/2.50  --res_time_limit                        2.
% 15.67/2.50  --res_out_proof                         true
% 15.67/2.50  
% 15.67/2.50  ------ Superposition Options
% 15.67/2.50  
% 15.67/2.50  --superposition_flag                    true
% 15.67/2.50  --sup_passive_queue_type                priority_queues
% 15.67/2.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.67/2.50  --sup_passive_queues_freq               [8;1;4]
% 15.67/2.50  --demod_completeness_check              fast
% 15.67/2.50  --demod_use_ground                      true
% 15.67/2.50  --sup_to_prop_solver                    passive
% 15.67/2.50  --sup_prop_simpl_new                    true
% 15.67/2.50  --sup_prop_simpl_given                  true
% 15.67/2.50  --sup_fun_splitting                     false
% 15.67/2.50  --sup_smt_interval                      50000
% 15.67/2.50  
% 15.67/2.50  ------ Superposition Simplification Setup
% 15.67/2.50  
% 15.67/2.50  --sup_indices_passive                   []
% 15.67/2.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.67/2.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.67/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.67/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 15.67/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.67/2.50  --sup_full_bw                           [BwDemod]
% 15.67/2.50  --sup_immed_triv                        [TrivRules]
% 15.67/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.67/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.67/2.50  --sup_immed_bw_main                     []
% 15.67/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.67/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 15.67/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.67/2.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.67/2.50  
% 15.67/2.50  ------ Combination Options
% 15.67/2.50  
% 15.67/2.50  --comb_res_mult                         3
% 15.67/2.50  --comb_sup_mult                         2
% 15.67/2.50  --comb_inst_mult                        10
% 15.67/2.50  
% 15.67/2.50  ------ Debug Options
% 15.67/2.50  
% 15.67/2.50  --dbg_backtrace                         false
% 15.67/2.50  --dbg_dump_prop_clauses                 false
% 15.67/2.50  --dbg_dump_prop_clauses_file            -
% 15.67/2.50  --dbg_out_stat                          false
% 15.67/2.50  
% 15.67/2.50  
% 15.67/2.50  
% 15.67/2.50  
% 15.67/2.50  ------ Proving...
% 15.67/2.50  
% 15.67/2.50  
% 15.67/2.50  % SZS status Theorem for theBenchmark.p
% 15.67/2.50  
% 15.67/2.50  % SZS output start CNFRefutation for theBenchmark.p
% 15.67/2.50  
% 15.67/2.50  fof(f11,conjecture,(
% 15.67/2.50    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1)))),
% 15.67/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.67/2.50  
% 15.67/2.50  fof(f12,negated_conjecture,(
% 15.67/2.50    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1)))),
% 15.67/2.50    inference(negated_conjecture,[],[f11])).
% 15.67/2.50  
% 15.67/2.50  fof(f33,plain,(
% 15.67/2.50    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)))),
% 15.67/2.50    inference(ennf_transformation,[],[f12])).
% 15.67/2.50  
% 15.67/2.50  fof(f34,plain,(
% 15.67/2.50    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 15.67/2.50    inference(flattening,[],[f33])).
% 15.67/2.50  
% 15.67/2.50  fof(f47,plain,(
% 15.67/2.50    ( ! [X0,X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) => (k12_lattice3(X0,X1,k13_lattice3(X0,X1,sK4)) != X1 & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 15.67/2.50    introduced(choice_axiom,[])).
% 15.67/2.50  
% 15.67/2.50  fof(f46,plain,(
% 15.67/2.50    ( ! [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k12_lattice3(X0,sK3,k13_lattice3(X0,sK3,X2)) != sK3 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 15.67/2.50    introduced(choice_axiom,[])).
% 15.67/2.50  
% 15.67/2.50  fof(f45,plain,(
% 15.67/2.50    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => (? [X1] : (? [X2] : (k12_lattice3(sK2,X1,k13_lattice3(sK2,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_orders_2(sK2) & v2_lattice3(sK2) & v1_lattice3(sK2) & v5_orders_2(sK2) & v3_orders_2(sK2))),
% 15.67/2.50    introduced(choice_axiom,[])).
% 15.67/2.50  
% 15.67/2.50  fof(f48,plain,(
% 15.67/2.50    ((k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 & m1_subset_1(sK4,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_orders_2(sK2) & v2_lattice3(sK2) & v1_lattice3(sK2) & v5_orders_2(sK2) & v3_orders_2(sK2)),
% 15.67/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f34,f47,f46,f45])).
% 15.67/2.50  
% 15.67/2.50  fof(f76,plain,(
% 15.67/2.50    m1_subset_1(sK3,u1_struct_0(sK2))),
% 15.67/2.50    inference(cnf_transformation,[],[f48])).
% 15.67/2.50  
% 15.67/2.50  fof(f4,axiom,(
% 15.67/2.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 15.67/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.67/2.50  
% 15.67/2.50  fof(f19,plain,(
% 15.67/2.50    ! [X0,X1,X2] : (m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 15.67/2.50    inference(ennf_transformation,[],[f4])).
% 15.67/2.50  
% 15.67/2.50  fof(f20,plain,(
% 15.67/2.50    ! [X0,X1,X2] : (m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 15.67/2.50    inference(flattening,[],[f19])).
% 15.67/2.50  
% 15.67/2.50  fof(f52,plain,(
% 15.67/2.50    ( ! [X2,X0,X1] : (m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 15.67/2.50    inference(cnf_transformation,[],[f20])).
% 15.67/2.50  
% 15.67/2.50  fof(f75,plain,(
% 15.67/2.50    l1_orders_2(sK2)),
% 15.67/2.50    inference(cnf_transformation,[],[f48])).
% 15.67/2.50  
% 15.67/2.50  fof(f72,plain,(
% 15.67/2.50    v5_orders_2(sK2)),
% 15.67/2.50    inference(cnf_transformation,[],[f48])).
% 15.67/2.50  
% 15.67/2.50  fof(f74,plain,(
% 15.67/2.50    v2_lattice3(sK2)),
% 15.67/2.50    inference(cnf_transformation,[],[f48])).
% 15.67/2.50  
% 15.67/2.50  fof(f9,axiom,(
% 15.67/2.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2))),
% 15.67/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.67/2.50  
% 15.67/2.50  fof(f29,plain,(
% 15.67/2.50    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 15.67/2.50    inference(ennf_transformation,[],[f9])).
% 15.67/2.50  
% 15.67/2.50  fof(f30,plain,(
% 15.67/2.50    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 15.67/2.50    inference(flattening,[],[f29])).
% 15.67/2.50  
% 15.67/2.50  fof(f69,plain,(
% 15.67/2.50    ( ! [X2,X0,X1] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 15.67/2.50    inference(cnf_transformation,[],[f30])).
% 15.67/2.50  
% 15.67/2.50  fof(f73,plain,(
% 15.67/2.50    v1_lattice3(sK2)),
% 15.67/2.50    inference(cnf_transformation,[],[f48])).
% 15.67/2.50  
% 15.67/2.50  fof(f10,axiom,(
% 15.67/2.50    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2)))),
% 15.67/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.67/2.50  
% 15.67/2.50  fof(f31,plain,(
% 15.67/2.50    ! [X0] : (! [X1] : (! [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)))),
% 15.67/2.50    inference(ennf_transformation,[],[f10])).
% 15.67/2.50  
% 15.67/2.50  fof(f32,plain,(
% 15.67/2.50    ! [X0] : (! [X1] : (! [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 15.67/2.50    inference(flattening,[],[f31])).
% 15.67/2.50  
% 15.67/2.50  fof(f70,plain,(
% 15.67/2.50    ( ! [X2,X0,X1] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)) )),
% 15.67/2.50    inference(cnf_transformation,[],[f32])).
% 15.67/2.50  
% 15.67/2.50  fof(f71,plain,(
% 15.67/2.50    v3_orders_2(sK2)),
% 15.67/2.50    inference(cnf_transformation,[],[f48])).
% 15.67/2.50  
% 15.67/2.50  fof(f6,axiom,(
% 15.67/2.50    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 15.67/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.67/2.50  
% 15.67/2.50  fof(f23,plain,(
% 15.67/2.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 15.67/2.50    inference(ennf_transformation,[],[f6])).
% 15.67/2.50  
% 15.67/2.50  fof(f24,plain,(
% 15.67/2.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 15.67/2.50    inference(flattening,[],[f23])).
% 15.67/2.50  
% 15.67/2.50  fof(f35,plain,(
% 15.67/2.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3))) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 15.67/2.50    inference(nnf_transformation,[],[f24])).
% 15.67/2.50  
% 15.67/2.50  fof(f36,plain,(
% 15.67/2.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 15.67/2.50    inference(flattening,[],[f35])).
% 15.67/2.50  
% 15.67/2.50  fof(f37,plain,(
% 15.67/2.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 15.67/2.50    inference(rectify,[],[f36])).
% 15.67/2.50  
% 15.67/2.50  fof(f38,plain,(
% 15.67/2.50    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,X3,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))))),
% 15.67/2.50    introduced(choice_axiom,[])).
% 15.67/2.50  
% 15.67/2.50  fof(f39,plain,(
% 15.67/2.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,X3,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 15.67/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 15.67/2.50  
% 15.67/2.50  fof(f55,plain,(
% 15.67/2.50    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X2,X3) | k10_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 15.67/2.50    inference(cnf_transformation,[],[f39])).
% 15.67/2.50  
% 15.67/2.50  fof(f80,plain,(
% 15.67/2.50    ( ! [X2,X0,X1] : (r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 15.67/2.50    inference(equality_resolution,[],[f55])).
% 15.67/2.50  
% 15.67/2.50  fof(f1,axiom,(
% 15.67/2.50    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 15.67/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.67/2.50  
% 15.67/2.50  fof(f13,plain,(
% 15.67/2.50    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 15.67/2.50    inference(ennf_transformation,[],[f1])).
% 15.67/2.50  
% 15.67/2.50  fof(f14,plain,(
% 15.67/2.50    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 15.67/2.50    inference(flattening,[],[f13])).
% 15.67/2.50  
% 15.67/2.50  fof(f49,plain,(
% 15.67/2.50    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 15.67/2.50    inference(cnf_transformation,[],[f14])).
% 15.67/2.50  
% 15.67/2.50  fof(f7,axiom,(
% 15.67/2.50    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 15.67/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.67/2.50  
% 15.67/2.50  fof(f25,plain,(
% 15.67/2.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 15.67/2.50    inference(ennf_transformation,[],[f7])).
% 15.67/2.50  
% 15.67/2.50  fof(f26,plain,(
% 15.67/2.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 15.67/2.50    inference(flattening,[],[f25])).
% 15.67/2.50  
% 15.67/2.50  fof(f40,plain,(
% 15.67/2.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 15.67/2.50    inference(nnf_transformation,[],[f26])).
% 15.67/2.50  
% 15.67/2.50  fof(f41,plain,(
% 15.67/2.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 15.67/2.50    inference(flattening,[],[f40])).
% 15.67/2.50  
% 15.67/2.50  fof(f42,plain,(
% 15.67/2.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 15.67/2.50    inference(rectify,[],[f41])).
% 15.67/2.50  
% 15.67/2.50  fof(f43,plain,(
% 15.67/2.50    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK1(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X1) & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0))))),
% 15.67/2.50    introduced(choice_axiom,[])).
% 15.67/2.50  
% 15.67/2.50  fof(f44,plain,(
% 15.67/2.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,sK1(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X1) & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 15.67/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f42,f43])).
% 15.67/2.50  
% 15.67/2.50  fof(f67,plain,(
% 15.67/2.50    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,sK1(X0,X1,X2,X3),X3) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 15.67/2.50    inference(cnf_transformation,[],[f44])).
% 15.67/2.50  
% 15.67/2.50  fof(f2,axiom,(
% 15.67/2.50    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 15.67/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.67/2.50  
% 15.67/2.50  fof(f15,plain,(
% 15.67/2.50    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 15.67/2.50    inference(ennf_transformation,[],[f2])).
% 15.67/2.50  
% 15.67/2.50  fof(f16,plain,(
% 15.67/2.50    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 15.67/2.50    inference(flattening,[],[f15])).
% 15.67/2.50  
% 15.67/2.50  fof(f50,plain,(
% 15.67/2.50    ( ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0)) )),
% 15.67/2.50    inference(cnf_transformation,[],[f16])).
% 15.67/2.50  
% 15.67/2.50  fof(f65,plain,(
% 15.67/2.50    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | r1_orders_2(X0,sK1(X0,X1,X2,X3),X1) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 15.67/2.50    inference(cnf_transformation,[],[f44])).
% 15.67/2.50  
% 15.67/2.50  fof(f77,plain,(
% 15.67/2.50    m1_subset_1(sK4,u1_struct_0(sK2))),
% 15.67/2.50    inference(cnf_transformation,[],[f48])).
% 15.67/2.50  
% 15.67/2.50  fof(f54,plain,(
% 15.67/2.50    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X1,X3) | k10_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 15.67/2.50    inference(cnf_transformation,[],[f39])).
% 15.67/2.50  
% 15.67/2.50  fof(f81,plain,(
% 15.67/2.50    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 15.67/2.50    inference(equality_resolution,[],[f54])).
% 15.67/2.50  
% 15.67/2.50  fof(f8,axiom,(
% 15.67/2.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2))),
% 15.67/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.67/2.50  
% 15.67/2.50  fof(f27,plain,(
% 15.67/2.50    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 15.67/2.50    inference(ennf_transformation,[],[f8])).
% 15.67/2.50  
% 15.67/2.50  fof(f28,plain,(
% 15.67/2.50    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 15.67/2.50    inference(flattening,[],[f27])).
% 15.67/2.50  
% 15.67/2.50  fof(f68,plain,(
% 15.67/2.50    ( ! [X2,X0,X1] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 15.67/2.50    inference(cnf_transformation,[],[f28])).
% 15.67/2.50  
% 15.67/2.50  fof(f5,axiom,(
% 15.67/2.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 15.67/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.67/2.50  
% 15.67/2.50  fof(f21,plain,(
% 15.67/2.50    ! [X0,X1,X2] : (m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 15.67/2.50    inference(ennf_transformation,[],[f5])).
% 15.67/2.50  
% 15.67/2.50  fof(f22,plain,(
% 15.67/2.50    ! [X0,X1,X2] : (m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 15.67/2.50    inference(flattening,[],[f21])).
% 15.67/2.50  
% 15.67/2.50  fof(f53,plain,(
% 15.67/2.50    ( ! [X2,X0,X1] : (m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 15.67/2.50    inference(cnf_transformation,[],[f22])).
% 15.67/2.50  
% 15.67/2.50  fof(f78,plain,(
% 15.67/2.50    k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3),
% 15.67/2.50    inference(cnf_transformation,[],[f48])).
% 15.67/2.50  
% 15.67/2.50  cnf(c_24,negated_conjecture,
% 15.67/2.50      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 15.67/2.50      inference(cnf_transformation,[],[f76]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_1209,negated_conjecture,
% 15.67/2.50      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 15.67/2.50      inference(subtyping,[status(esa)],[c_24]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_1592,plain,
% 15.67/2.50      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 15.67/2.50      inference(predicate_to_equality,[status(thm)],[c_1209]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_3,plain,
% 15.67/2.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.67/2.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.67/2.50      | m1_subset_1(k12_lattice3(X1,X2,X0),u1_struct_0(X1))
% 15.67/2.50      | ~ v5_orders_2(X1)
% 15.67/2.50      | ~ v2_lattice3(X1)
% 15.67/2.50      | ~ l1_orders_2(X1) ),
% 15.67/2.50      inference(cnf_transformation,[],[f52]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_25,negated_conjecture,
% 15.67/2.50      ( l1_orders_2(sK2) ),
% 15.67/2.50      inference(cnf_transformation,[],[f75]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_941,plain,
% 15.67/2.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.67/2.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.67/2.50      | m1_subset_1(k12_lattice3(X1,X2,X0),u1_struct_0(X1))
% 15.67/2.50      | ~ v5_orders_2(X1)
% 15.67/2.50      | ~ v2_lattice3(X1)
% 15.67/2.50      | sK2 != X1 ),
% 15.67/2.50      inference(resolution_lifted,[status(thm)],[c_3,c_25]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_942,plain,
% 15.67/2.50      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 15.67/2.50      | m1_subset_1(k12_lattice3(sK2,X0,X1),u1_struct_0(sK2))
% 15.67/2.50      | ~ v5_orders_2(sK2)
% 15.67/2.50      | ~ v2_lattice3(sK2) ),
% 15.67/2.50      inference(unflattening,[status(thm)],[c_941]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_28,negated_conjecture,
% 15.67/2.50      ( v5_orders_2(sK2) ),
% 15.67/2.50      inference(cnf_transformation,[],[f72]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_26,negated_conjecture,
% 15.67/2.50      ( v2_lattice3(sK2) ),
% 15.67/2.50      inference(cnf_transformation,[],[f74]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_946,plain,
% 15.67/2.50      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 15.67/2.50      | m1_subset_1(k12_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
% 15.67/2.50      inference(global_propositional_subsumption,
% 15.67/2.50                [status(thm)],
% 15.67/2.50                [c_942,c_28,c_26]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_1190,plain,
% 15.67/2.50      ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 15.67/2.50      | m1_subset_1(k12_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) ),
% 15.67/2.50      inference(subtyping,[status(esa)],[c_946]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_1611,plain,
% 15.67/2.50      ( m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 15.67/2.50      | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top
% 15.67/2.50      | m1_subset_1(k12_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) = iProver_top ),
% 15.67/2.50      inference(predicate_to_equality,[status(thm)],[c_1190]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_20,plain,
% 15.67/2.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.67/2.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.67/2.50      | ~ v5_orders_2(X1)
% 15.67/2.50      | ~ l1_orders_2(X1)
% 15.67/2.50      | ~ v1_lattice3(X1)
% 15.67/2.50      | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0) ),
% 15.67/2.50      inference(cnf_transformation,[],[f69]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_27,negated_conjecture,
% 15.67/2.50      ( v1_lattice3(sK2) ),
% 15.67/2.50      inference(cnf_transformation,[],[f73]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_615,plain,
% 15.67/2.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.67/2.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.67/2.50      | ~ v5_orders_2(X1)
% 15.67/2.50      | ~ l1_orders_2(X1)
% 15.67/2.50      | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0)
% 15.67/2.50      | sK2 != X1 ),
% 15.67/2.50      inference(resolution_lifted,[status(thm)],[c_20,c_27]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_616,plain,
% 15.67/2.50      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 15.67/2.50      | ~ v5_orders_2(sK2)
% 15.67/2.50      | ~ l1_orders_2(sK2)
% 15.67/2.50      | k10_lattice3(sK2,X0,X1) = k13_lattice3(sK2,X0,X1) ),
% 15.67/2.50      inference(unflattening,[status(thm)],[c_615]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_620,plain,
% 15.67/2.50      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 15.67/2.50      | k10_lattice3(sK2,X0,X1) = k13_lattice3(sK2,X0,X1) ),
% 15.67/2.50      inference(global_propositional_subsumption,
% 15.67/2.50                [status(thm)],
% 15.67/2.50                [c_616,c_28,c_25]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_1200,plain,
% 15.67/2.50      ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 15.67/2.50      | k10_lattice3(sK2,X0_46,X1_46) = k13_lattice3(sK2,X0_46,X1_46) ),
% 15.67/2.50      inference(subtyping,[status(esa)],[c_620]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_1601,plain,
% 15.67/2.50      ( k10_lattice3(sK2,X0_46,X1_46) = k13_lattice3(sK2,X0_46,X1_46)
% 15.67/2.50      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 15.67/2.50      | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top ),
% 15.67/2.50      inference(predicate_to_equality,[status(thm)],[c_1200]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_3941,plain,
% 15.67/2.50      ( k10_lattice3(sK2,k12_lattice3(sK2,X0_46,X1_46),X2_46) = k13_lattice3(sK2,k12_lattice3(sK2,X0_46,X1_46),X2_46)
% 15.67/2.50      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 15.67/2.50      | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top
% 15.67/2.50      | m1_subset_1(X2_46,u1_struct_0(sK2)) != iProver_top ),
% 15.67/2.50      inference(superposition,[status(thm)],[c_1611,c_1601]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_32756,plain,
% 15.67/2.50      ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,X0_46),X1_46) = k13_lattice3(sK2,k12_lattice3(sK2,sK3,X0_46),X1_46)
% 15.67/2.50      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 15.67/2.50      | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top ),
% 15.67/2.50      inference(superposition,[status(thm)],[c_1592,c_3941]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_37005,plain,
% 15.67/2.50      ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK3),X0_46) = k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK3),X0_46)
% 15.67/2.50      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top ),
% 15.67/2.50      inference(superposition,[status(thm)],[c_1592,c_32756]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_37879,plain,
% 15.67/2.50      ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK3),sK3) = k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK3),sK3) ),
% 15.67/2.50      inference(superposition,[status(thm)],[c_1592,c_37005]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_21,plain,
% 15.67/2.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.67/2.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.67/2.50      | ~ v3_orders_2(X1)
% 15.67/2.50      | ~ v5_orders_2(X1)
% 15.67/2.50      | ~ v2_lattice3(X1)
% 15.67/2.50      | ~ l1_orders_2(X1)
% 15.67/2.50      | ~ v1_lattice3(X1)
% 15.67/2.50      | k13_lattice3(X1,k12_lattice3(X1,X2,X0),X0) = X0 ),
% 15.67/2.50      inference(cnf_transformation,[],[f70]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_29,negated_conjecture,
% 15.67/2.50      ( v3_orders_2(sK2) ),
% 15.67/2.50      inference(cnf_transformation,[],[f71]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_385,plain,
% 15.67/2.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.67/2.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.67/2.50      | ~ v5_orders_2(X1)
% 15.67/2.50      | ~ v2_lattice3(X1)
% 15.67/2.50      | ~ l1_orders_2(X1)
% 15.67/2.50      | ~ v1_lattice3(X1)
% 15.67/2.50      | k13_lattice3(X1,k12_lattice3(X1,X2,X0),X0) = X0
% 15.67/2.50      | sK2 != X1 ),
% 15.67/2.50      inference(resolution_lifted,[status(thm)],[c_21,c_29]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_386,plain,
% 15.67/2.50      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 15.67/2.50      | ~ v5_orders_2(sK2)
% 15.67/2.50      | ~ v2_lattice3(sK2)
% 15.67/2.50      | ~ l1_orders_2(sK2)
% 15.67/2.50      | ~ v1_lattice3(sK2)
% 15.67/2.50      | k13_lattice3(sK2,k12_lattice3(sK2,X0,X1),X1) = X1 ),
% 15.67/2.50      inference(unflattening,[status(thm)],[c_385]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_390,plain,
% 15.67/2.50      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 15.67/2.50      | k13_lattice3(sK2,k12_lattice3(sK2,X0,X1),X1) = X1 ),
% 15.67/2.50      inference(global_propositional_subsumption,
% 15.67/2.50                [status(thm)],
% 15.67/2.50                [c_386,c_28,c_27,c_26,c_25]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_1208,plain,
% 15.67/2.50      ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 15.67/2.50      | k13_lattice3(sK2,k12_lattice3(sK2,X0_46,X1_46),X1_46) = X1_46 ),
% 15.67/2.50      inference(subtyping,[status(esa)],[c_390]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_1593,plain,
% 15.67/2.50      ( k13_lattice3(sK2,k12_lattice3(sK2,X0_46,X1_46),X1_46) = X1_46
% 15.67/2.50      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 15.67/2.50      | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top ),
% 15.67/2.50      inference(predicate_to_equality,[status(thm)],[c_1208]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_1883,plain,
% 15.67/2.50      ( k13_lattice3(sK2,k12_lattice3(sK2,sK3,X0_46),X0_46) = X0_46
% 15.67/2.50      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top ),
% 15.67/2.50      inference(superposition,[status(thm)],[c_1592,c_1593]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_2008,plain,
% 15.67/2.50      ( k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK3),sK3) = sK3 ),
% 15.67/2.50      inference(superposition,[status(thm)],[c_1592,c_1883]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_37925,plain,
% 15.67/2.50      ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK3),sK3) = sK3 ),
% 15.67/2.50      inference(light_normalisation,[status(thm)],[c_37879,c_2008]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_10,plain,
% 15.67/2.50      ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
% 15.67/2.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.67/2.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.67/2.50      | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
% 15.67/2.50      | ~ v5_orders_2(X0)
% 15.67/2.50      | ~ l1_orders_2(X0)
% 15.67/2.50      | ~ v1_lattice3(X0)
% 15.67/2.50      | v2_struct_0(X0) ),
% 15.67/2.50      inference(cnf_transformation,[],[f80]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_0,plain,
% 15.67/2.50      ( ~ l1_orders_2(X0) | ~ v1_lattice3(X0) | ~ v2_struct_0(X0) ),
% 15.67/2.50      inference(cnf_transformation,[],[f49]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_216,plain,
% 15.67/2.50      ( ~ v1_lattice3(X0)
% 15.67/2.50      | ~ l1_orders_2(X0)
% 15.67/2.50      | ~ v5_orders_2(X0)
% 15.67/2.50      | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
% 15.67/2.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.67/2.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.67/2.50      | r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1)) ),
% 15.67/2.50      inference(global_propositional_subsumption,
% 15.67/2.50                [status(thm)],
% 15.67/2.50                [c_10,c_0]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_217,plain,
% 15.67/2.50      ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
% 15.67/2.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.67/2.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.67/2.50      | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
% 15.67/2.50      | ~ v5_orders_2(X0)
% 15.67/2.50      | ~ l1_orders_2(X0)
% 15.67/2.50      | ~ v1_lattice3(X0) ),
% 15.67/2.50      inference(renaming,[status(thm)],[c_216]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_571,plain,
% 15.67/2.50      ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
% 15.67/2.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.67/2.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.67/2.50      | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
% 15.67/2.50      | ~ v5_orders_2(X0)
% 15.67/2.50      | ~ l1_orders_2(X0)
% 15.67/2.50      | sK2 != X0 ),
% 15.67/2.50      inference(resolution_lifted,[status(thm)],[c_217,c_27]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_572,plain,
% 15.67/2.50      ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X1,X0))
% 15.67/2.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(k10_lattice3(sK2,X1,X0),u1_struct_0(sK2))
% 15.67/2.50      | ~ v5_orders_2(sK2)
% 15.67/2.50      | ~ l1_orders_2(sK2) ),
% 15.67/2.50      inference(unflattening,[status(thm)],[c_571]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_576,plain,
% 15.67/2.50      ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X1,X0))
% 15.67/2.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(k10_lattice3(sK2,X1,X0),u1_struct_0(sK2)) ),
% 15.67/2.50      inference(global_propositional_subsumption,
% 15.67/2.50                [status(thm)],
% 15.67/2.50                [c_572,c_28,c_25]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_577,plain,
% 15.67/2.50      ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X1,X0))
% 15.67/2.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(k10_lattice3(sK2,X1,X0),u1_struct_0(sK2)) ),
% 15.67/2.50      inference(renaming,[status(thm)],[c_576]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_1202,plain,
% 15.67/2.50      ( r1_orders_2(sK2,X0_46,k10_lattice3(sK2,X1_46,X0_46))
% 15.67/2.50      | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(k10_lattice3(sK2,X1_46,X0_46),u1_struct_0(sK2)) ),
% 15.67/2.50      inference(subtyping,[status(esa)],[c_577]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_1599,plain,
% 15.67/2.50      ( r1_orders_2(sK2,X0_46,k10_lattice3(sK2,X1_46,X0_46)) = iProver_top
% 15.67/2.50      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 15.67/2.50      | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top
% 15.67/2.50      | m1_subset_1(k10_lattice3(sK2,X1_46,X0_46),u1_struct_0(sK2)) != iProver_top ),
% 15.67/2.50      inference(predicate_to_equality,[status(thm)],[c_1202]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_38614,plain,
% 15.67/2.50      ( r1_orders_2(sK2,sK3,k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK3),sK3)) = iProver_top
% 15.67/2.50      | m1_subset_1(k12_lattice3(sK2,sK3,sK3),u1_struct_0(sK2)) != iProver_top
% 15.67/2.50      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 15.67/2.50      inference(superposition,[status(thm)],[c_37925,c_1599]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_38626,plain,
% 15.67/2.50      ( r1_orders_2(sK2,sK3,sK3) = iProver_top
% 15.67/2.50      | m1_subset_1(k12_lattice3(sK2,sK3,sK3),u1_struct_0(sK2)) != iProver_top
% 15.67/2.50      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 15.67/2.50      inference(light_normalisation,[status(thm)],[c_38614,c_37925]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_12,plain,
% 15.67/2.50      ( ~ r1_orders_2(X0,X1,X2)
% 15.67/2.50      | ~ r1_orders_2(X0,X1,X3)
% 15.67/2.50      | ~ r1_orders_2(X0,sK1(X0,X3,X2,X1),X1)
% 15.67/2.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.67/2.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 15.67/2.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.67/2.50      | ~ v5_orders_2(X0)
% 15.67/2.50      | ~ v2_lattice3(X0)
% 15.67/2.50      | ~ l1_orders_2(X0)
% 15.67/2.50      | v2_struct_0(X0)
% 15.67/2.50      | k11_lattice3(X0,X3,X2) = X1 ),
% 15.67/2.50      inference(cnf_transformation,[],[f67]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_1,plain,
% 15.67/2.50      ( ~ v2_lattice3(X0) | ~ l1_orders_2(X0) | ~ v2_struct_0(X0) ),
% 15.67/2.50      inference(cnf_transformation,[],[f50]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_202,plain,
% 15.67/2.50      ( ~ l1_orders_2(X0)
% 15.67/2.50      | ~ v2_lattice3(X0)
% 15.67/2.50      | ~ v5_orders_2(X0)
% 15.67/2.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.67/2.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 15.67/2.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.67/2.50      | ~ r1_orders_2(X0,sK1(X0,X3,X2,X1),X1)
% 15.67/2.50      | ~ r1_orders_2(X0,X1,X3)
% 15.67/2.50      | ~ r1_orders_2(X0,X1,X2)
% 15.67/2.50      | k11_lattice3(X0,X3,X2) = X1 ),
% 15.67/2.50      inference(global_propositional_subsumption,
% 15.67/2.50                [status(thm)],
% 15.67/2.50                [c_12,c_1]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_203,plain,
% 15.67/2.50      ( ~ r1_orders_2(X0,X1,X2)
% 15.67/2.50      | ~ r1_orders_2(X0,X1,X3)
% 15.67/2.50      | ~ r1_orders_2(X0,sK1(X0,X2,X3,X1),X1)
% 15.67/2.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 15.67/2.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.67/2.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.67/2.50      | ~ v5_orders_2(X0)
% 15.67/2.50      | ~ v2_lattice3(X0)
% 15.67/2.50      | ~ l1_orders_2(X0)
% 15.67/2.50      | k11_lattice3(X0,X2,X3) = X1 ),
% 15.67/2.50      inference(renaming,[status(thm)],[c_202]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_715,plain,
% 15.67/2.50      ( ~ r1_orders_2(X0,X1,X2)
% 15.67/2.50      | ~ r1_orders_2(X0,X1,X3)
% 15.67/2.50      | ~ r1_orders_2(X0,sK1(X0,X3,X2,X1),X1)
% 15.67/2.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 15.67/2.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.67/2.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.67/2.50      | ~ v5_orders_2(X0)
% 15.67/2.50      | ~ v2_lattice3(X0)
% 15.67/2.50      | k11_lattice3(X0,X3,X2) = X1
% 15.67/2.50      | sK2 != X0 ),
% 15.67/2.50      inference(resolution_lifted,[status(thm)],[c_203,c_25]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_716,plain,
% 15.67/2.50      ( ~ r1_orders_2(sK2,X0,X1)
% 15.67/2.50      | ~ r1_orders_2(sK2,X0,X2)
% 15.67/2.50      | ~ r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X0)
% 15.67/2.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 15.67/2.50      | ~ v5_orders_2(sK2)
% 15.67/2.50      | ~ v2_lattice3(sK2)
% 15.67/2.50      | k11_lattice3(sK2,X2,X1) = X0 ),
% 15.67/2.50      inference(unflattening,[status(thm)],[c_715]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_720,plain,
% 15.67/2.50      ( ~ r1_orders_2(sK2,X0,X1)
% 15.67/2.50      | ~ r1_orders_2(sK2,X0,X2)
% 15.67/2.50      | ~ r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X0)
% 15.67/2.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 15.67/2.50      | k11_lattice3(sK2,X2,X1) = X0 ),
% 15.67/2.50      inference(global_propositional_subsumption,
% 15.67/2.50                [status(thm)],
% 15.67/2.50                [c_716,c_28,c_26]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_721,plain,
% 15.67/2.50      ( ~ r1_orders_2(sK2,X0,X1)
% 15.67/2.50      | ~ r1_orders_2(sK2,X0,X2)
% 15.67/2.50      | ~ r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X0)
% 15.67/2.50      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 15.67/2.50      | k11_lattice3(sK2,X2,X1) = X0 ),
% 15.67/2.50      inference(renaming,[status(thm)],[c_720]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_1198,plain,
% 15.67/2.50      ( ~ r1_orders_2(sK2,X0_46,X1_46)
% 15.67/2.50      | ~ r1_orders_2(sK2,X0_46,X2_46)
% 15.67/2.50      | ~ r1_orders_2(sK2,sK1(sK2,X2_46,X1_46,X0_46),X0_46)
% 15.67/2.50      | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(X2_46,u1_struct_0(sK2))
% 15.67/2.50      | k11_lattice3(sK2,X2_46,X1_46) = X0_46 ),
% 15.67/2.50      inference(subtyping,[status(esa)],[c_721]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_9517,plain,
% 15.67/2.50      ( ~ r1_orders_2(sK2,X0_46,k13_lattice3(sK2,sK3,sK4))
% 15.67/2.50      | ~ r1_orders_2(sK2,X0_46,sK3)
% 15.67/2.50      | ~ r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_46),X0_46)
% 15.67/2.50      | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 15.67/2.50      | k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46 ),
% 15.67/2.50      inference(instantiation,[status(thm)],[c_1198]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_9533,plain,
% 15.67/2.50      ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46
% 15.67/2.50      | r1_orders_2(sK2,X0_46,k13_lattice3(sK2,sK3,sK4)) != iProver_top
% 15.67/2.50      | r1_orders_2(sK2,X0_46,sK3) != iProver_top
% 15.67/2.50      | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_46),X0_46) != iProver_top
% 15.67/2.50      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 15.67/2.50      | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 15.67/2.50      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 15.67/2.50      inference(predicate_to_equality,[status(thm)],[c_9517]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_9535,plain,
% 15.67/2.50      ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
% 15.67/2.50      | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),sK3),sK3) != iProver_top
% 15.67/2.50      | r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != iProver_top
% 15.67/2.50      | r1_orders_2(sK2,sK3,sK3) != iProver_top
% 15.67/2.50      | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 15.67/2.50      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 15.67/2.50      inference(instantiation,[status(thm)],[c_9533]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_14,plain,
% 15.67/2.50      ( ~ r1_orders_2(X0,X1,X2)
% 15.67/2.50      | ~ r1_orders_2(X0,X1,X3)
% 15.67/2.50      | r1_orders_2(X0,sK1(X0,X3,X2,X1),X3)
% 15.67/2.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.67/2.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 15.67/2.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.67/2.50      | ~ v5_orders_2(X0)
% 15.67/2.50      | ~ v2_lattice3(X0)
% 15.67/2.50      | ~ l1_orders_2(X0)
% 15.67/2.50      | v2_struct_0(X0)
% 15.67/2.50      | k11_lattice3(X0,X3,X2) = X1 ),
% 15.67/2.50      inference(cnf_transformation,[],[f65]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_190,plain,
% 15.67/2.50      ( ~ l1_orders_2(X0)
% 15.67/2.50      | ~ v2_lattice3(X0)
% 15.67/2.50      | ~ v5_orders_2(X0)
% 15.67/2.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.67/2.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 15.67/2.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.67/2.50      | r1_orders_2(X0,sK1(X0,X3,X2,X1),X3)
% 15.67/2.50      | ~ r1_orders_2(X0,X1,X3)
% 15.67/2.50      | ~ r1_orders_2(X0,X1,X2)
% 15.67/2.50      | k11_lattice3(X0,X3,X2) = X1 ),
% 15.67/2.50      inference(global_propositional_subsumption,
% 15.67/2.50                [status(thm)],
% 15.67/2.50                [c_14,c_1]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_191,plain,
% 15.67/2.50      ( ~ r1_orders_2(X0,X1,X2)
% 15.67/2.50      | ~ r1_orders_2(X0,X1,X3)
% 15.67/2.50      | r1_orders_2(X0,sK1(X0,X2,X3,X1),X2)
% 15.67/2.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 15.67/2.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.67/2.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.67/2.50      | ~ v5_orders_2(X0)
% 15.67/2.50      | ~ v2_lattice3(X0)
% 15.67/2.50      | ~ l1_orders_2(X0)
% 15.67/2.50      | k11_lattice3(X0,X2,X3) = X1 ),
% 15.67/2.50      inference(renaming,[status(thm)],[c_190]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_781,plain,
% 15.67/2.50      ( ~ r1_orders_2(X0,X1,X2)
% 15.67/2.50      | ~ r1_orders_2(X0,X1,X3)
% 15.67/2.50      | r1_orders_2(X0,sK1(X0,X3,X2,X1),X3)
% 15.67/2.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 15.67/2.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.67/2.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.67/2.50      | ~ v5_orders_2(X0)
% 15.67/2.50      | ~ v2_lattice3(X0)
% 15.67/2.50      | k11_lattice3(X0,X3,X2) = X1
% 15.67/2.50      | sK2 != X0 ),
% 15.67/2.50      inference(resolution_lifted,[status(thm)],[c_191,c_25]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_782,plain,
% 15.67/2.50      ( ~ r1_orders_2(sK2,X0,X1)
% 15.67/2.50      | ~ r1_orders_2(sK2,X0,X2)
% 15.67/2.50      | r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X2)
% 15.67/2.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 15.67/2.50      | ~ v5_orders_2(sK2)
% 15.67/2.50      | ~ v2_lattice3(sK2)
% 15.67/2.50      | k11_lattice3(sK2,X2,X1) = X0 ),
% 15.67/2.50      inference(unflattening,[status(thm)],[c_781]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_784,plain,
% 15.67/2.50      ( ~ r1_orders_2(sK2,X0,X1)
% 15.67/2.50      | ~ r1_orders_2(sK2,X0,X2)
% 15.67/2.50      | r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X2)
% 15.67/2.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 15.67/2.50      | k11_lattice3(sK2,X2,X1) = X0 ),
% 15.67/2.50      inference(global_propositional_subsumption,
% 15.67/2.50                [status(thm)],
% 15.67/2.50                [c_782,c_28,c_26]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_785,plain,
% 15.67/2.50      ( ~ r1_orders_2(sK2,X0,X1)
% 15.67/2.50      | ~ r1_orders_2(sK2,X0,X2)
% 15.67/2.50      | r1_orders_2(sK2,sK1(sK2,X2,X1,X0),X2)
% 15.67/2.50      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 15.67/2.50      | k11_lattice3(sK2,X2,X1) = X0 ),
% 15.67/2.50      inference(renaming,[status(thm)],[c_784]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_1196,plain,
% 15.67/2.50      ( ~ r1_orders_2(sK2,X0_46,X1_46)
% 15.67/2.50      | ~ r1_orders_2(sK2,X0_46,X2_46)
% 15.67/2.50      | r1_orders_2(sK2,sK1(sK2,X2_46,X1_46,X0_46),X2_46)
% 15.67/2.50      | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(X2_46,u1_struct_0(sK2))
% 15.67/2.50      | k11_lattice3(sK2,X2_46,X1_46) = X0_46 ),
% 15.67/2.50      inference(subtyping,[status(esa)],[c_785]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_9519,plain,
% 15.67/2.50      ( ~ r1_orders_2(sK2,X0_46,k13_lattice3(sK2,sK3,sK4))
% 15.67/2.50      | ~ r1_orders_2(sK2,X0_46,sK3)
% 15.67/2.50      | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_46),sK3)
% 15.67/2.50      | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 15.67/2.50      | k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46 ),
% 15.67/2.50      inference(instantiation,[status(thm)],[c_1196]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_9525,plain,
% 15.67/2.50      ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46
% 15.67/2.50      | r1_orders_2(sK2,X0_46,k13_lattice3(sK2,sK3,sK4)) != iProver_top
% 15.67/2.50      | r1_orders_2(sK2,X0_46,sK3) != iProver_top
% 15.67/2.50      | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_46),sK3) = iProver_top
% 15.67/2.50      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 15.67/2.50      | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 15.67/2.50      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 15.67/2.50      inference(predicate_to_equality,[status(thm)],[c_9519]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_9527,plain,
% 15.67/2.50      ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
% 15.67/2.50      | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),sK3),sK3) = iProver_top
% 15.67/2.50      | r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != iProver_top
% 15.67/2.50      | r1_orders_2(sK2,sK3,sK3) != iProver_top
% 15.67/2.50      | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 15.67/2.50      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 15.67/2.50      inference(instantiation,[status(thm)],[c_9525]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_23,negated_conjecture,
% 15.67/2.50      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 15.67/2.50      inference(cnf_transformation,[],[f77]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_1210,negated_conjecture,
% 15.67/2.50      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 15.67/2.50      inference(subtyping,[status(esa)],[c_23]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_1591,plain,
% 15.67/2.50      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 15.67/2.50      inference(predicate_to_equality,[status(thm)],[c_1210]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_2242,plain,
% 15.67/2.50      ( k10_lattice3(sK2,sK3,X0_46) = k13_lattice3(sK2,sK3,X0_46)
% 15.67/2.50      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top ),
% 15.67/2.50      inference(superposition,[status(thm)],[c_1592,c_1601]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_2360,plain,
% 15.67/2.50      ( k10_lattice3(sK2,sK3,sK4) = k13_lattice3(sK2,sK3,sK4) ),
% 15.67/2.50      inference(superposition,[status(thm)],[c_1591,c_2242]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_11,plain,
% 15.67/2.50      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 15.67/2.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.67/2.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.67/2.50      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 15.67/2.50      | ~ v5_orders_2(X0)
% 15.67/2.50      | ~ l1_orders_2(X0)
% 15.67/2.50      | ~ v1_lattice3(X0)
% 15.67/2.50      | v2_struct_0(X0) ),
% 15.67/2.50      inference(cnf_transformation,[],[f81]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_209,plain,
% 15.67/2.50      ( ~ v1_lattice3(X0)
% 15.67/2.50      | ~ l1_orders_2(X0)
% 15.67/2.50      | ~ v5_orders_2(X0)
% 15.67/2.50      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 15.67/2.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.67/2.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.67/2.50      | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) ),
% 15.67/2.50      inference(global_propositional_subsumption,
% 15.67/2.50                [status(thm)],
% 15.67/2.50                [c_11,c_0]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_210,plain,
% 15.67/2.50      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 15.67/2.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.67/2.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.67/2.50      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 15.67/2.50      | ~ v5_orders_2(X0)
% 15.67/2.50      | ~ l1_orders_2(X0)
% 15.67/2.50      | ~ v1_lattice3(X0) ),
% 15.67/2.50      inference(renaming,[status(thm)],[c_209]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_595,plain,
% 15.67/2.50      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 15.67/2.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.67/2.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.67/2.50      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 15.67/2.50      | ~ v5_orders_2(X0)
% 15.67/2.50      | ~ l1_orders_2(X0)
% 15.67/2.50      | sK2 != X0 ),
% 15.67/2.50      inference(resolution_lifted,[status(thm)],[c_210,c_27]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_596,plain,
% 15.67/2.50      ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
% 15.67/2.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2))
% 15.67/2.50      | ~ v5_orders_2(sK2)
% 15.67/2.50      | ~ l1_orders_2(sK2) ),
% 15.67/2.50      inference(unflattening,[status(thm)],[c_595]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_598,plain,
% 15.67/2.50      ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
% 15.67/2.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
% 15.67/2.50      inference(global_propositional_subsumption,
% 15.67/2.50                [status(thm)],
% 15.67/2.50                [c_596,c_28,c_25]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_599,plain,
% 15.67/2.50      ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
% 15.67/2.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
% 15.67/2.50      inference(renaming,[status(thm)],[c_598]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_1201,plain,
% 15.67/2.50      ( r1_orders_2(sK2,X0_46,k10_lattice3(sK2,X0_46,X1_46))
% 15.67/2.50      | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(k10_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) ),
% 15.67/2.50      inference(subtyping,[status(esa)],[c_599]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_1600,plain,
% 15.67/2.50      ( r1_orders_2(sK2,X0_46,k10_lattice3(sK2,X0_46,X1_46)) = iProver_top
% 15.67/2.50      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 15.67/2.50      | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top
% 15.67/2.50      | m1_subset_1(k10_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) != iProver_top ),
% 15.67/2.50      inference(predicate_to_equality,[status(thm)],[c_1201]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_4989,plain,
% 15.67/2.50      ( r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK4)) = iProver_top
% 15.67/2.50      | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 15.67/2.50      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 15.67/2.50      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 15.67/2.50      inference(superposition,[status(thm)],[c_2360,c_1600]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_4994,plain,
% 15.67/2.50      ( r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = iProver_top
% 15.67/2.50      | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 15.67/2.50      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 15.67/2.50      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 15.67/2.50      inference(light_normalisation,[status(thm)],[c_4989,c_2360]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_1214,plain,
% 15.67/2.50      ( X0_46 != X1_46 | X2_46 != X1_46 | X2_46 = X0_46 ),
% 15.67/2.50      theory(equality) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_2331,plain,
% 15.67/2.50      ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != X0_46
% 15.67/2.50      | sK3 != X0_46
% 15.67/2.50      | sK3 = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
% 15.67/2.50      inference(instantiation,[status(thm)],[c_1214]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_2332,plain,
% 15.67/2.50      ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3
% 15.67/2.50      | sK3 = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
% 15.67/2.50      | sK3 != sK3 ),
% 15.67/2.50      inference(instantiation,[status(thm)],[c_2331]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_1896,plain,
% 15.67/2.50      ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != X0_46
% 15.67/2.50      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
% 15.67/2.50      | sK3 != X0_46 ),
% 15.67/2.50      inference(instantiation,[status(thm)],[c_1214]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_2327,plain,
% 15.67/2.50      ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
% 15.67/2.50      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
% 15.67/2.50      | sK3 != k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
% 15.67/2.50      inference(instantiation,[status(thm)],[c_1896]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_19,plain,
% 15.67/2.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.67/2.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.67/2.50      | ~ v5_orders_2(X1)
% 15.67/2.50      | ~ v2_lattice3(X1)
% 15.67/2.50      | ~ l1_orders_2(X1)
% 15.67/2.50      | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0) ),
% 15.67/2.50      inference(cnf_transformation,[],[f68]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_920,plain,
% 15.67/2.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.67/2.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.67/2.50      | ~ v5_orders_2(X1)
% 15.67/2.50      | ~ v2_lattice3(X1)
% 15.67/2.50      | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0)
% 15.67/2.50      | sK2 != X1 ),
% 15.67/2.50      inference(resolution_lifted,[status(thm)],[c_19,c_25]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_921,plain,
% 15.67/2.50      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 15.67/2.50      | ~ v5_orders_2(sK2)
% 15.67/2.50      | ~ v2_lattice3(sK2)
% 15.67/2.50      | k11_lattice3(sK2,X0,X1) = k12_lattice3(sK2,X0,X1) ),
% 15.67/2.50      inference(unflattening,[status(thm)],[c_920]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_925,plain,
% 15.67/2.50      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 15.67/2.50      | k11_lattice3(sK2,X0,X1) = k12_lattice3(sK2,X0,X1) ),
% 15.67/2.50      inference(global_propositional_subsumption,
% 15.67/2.50                [status(thm)],
% 15.67/2.50                [c_921,c_28,c_26]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_1191,plain,
% 15.67/2.50      ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 15.67/2.50      | k11_lattice3(sK2,X0_46,X1_46) = k12_lattice3(sK2,X0_46,X1_46) ),
% 15.67/2.50      inference(subtyping,[status(esa)],[c_925]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_2276,plain,
% 15.67/2.50      ( ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 15.67/2.50      | k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
% 15.67/2.50      inference(instantiation,[status(thm)],[c_1191]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_1925,plain,
% 15.67/2.50      ( X0_46 != X1_46
% 15.67/2.50      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != X1_46
% 15.67/2.50      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46 ),
% 15.67/2.50      inference(instantiation,[status(thm)],[c_1214]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_2020,plain,
% 15.67/2.50      ( X0_46 != k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
% 15.67/2.50      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46
% 15.67/2.50      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
% 15.67/2.50      inference(instantiation,[status(thm)],[c_1925]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_2275,plain,
% 15.67/2.50      ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
% 15.67/2.50      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
% 15.67/2.50      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
% 15.67/2.50      inference(instantiation,[status(thm)],[c_2020]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_4,plain,
% 15.67/2.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.67/2.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.67/2.50      | m1_subset_1(k13_lattice3(X1,X2,X0),u1_struct_0(X1))
% 15.67/2.50      | ~ v5_orders_2(X1)
% 15.67/2.50      | ~ l1_orders_2(X1)
% 15.67/2.50      | ~ v1_lattice3(X1) ),
% 15.67/2.50      inference(cnf_transformation,[],[f53]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_636,plain,
% 15.67/2.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.67/2.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.67/2.50      | m1_subset_1(k13_lattice3(X1,X2,X0),u1_struct_0(X1))
% 15.67/2.50      | ~ v5_orders_2(X1)
% 15.67/2.50      | ~ l1_orders_2(X1)
% 15.67/2.50      | sK2 != X1 ),
% 15.67/2.50      inference(resolution_lifted,[status(thm)],[c_4,c_27]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_637,plain,
% 15.67/2.50      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 15.67/2.50      | m1_subset_1(k13_lattice3(sK2,X0,X1),u1_struct_0(sK2))
% 15.67/2.50      | ~ v5_orders_2(sK2)
% 15.67/2.50      | ~ l1_orders_2(sK2) ),
% 15.67/2.50      inference(unflattening,[status(thm)],[c_636]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_641,plain,
% 15.67/2.50      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 15.67/2.50      | m1_subset_1(k13_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
% 15.67/2.50      inference(global_propositional_subsumption,
% 15.67/2.50                [status(thm)],
% 15.67/2.50                [c_637,c_28,c_25]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_1199,plain,
% 15.67/2.50      ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 15.67/2.50      | m1_subset_1(k13_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) ),
% 15.67/2.50      inference(subtyping,[status(esa)],[c_641]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_1998,plain,
% 15.67/2.50      ( m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 15.67/2.50      | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 15.67/2.50      inference(instantiation,[status(thm)],[c_1199]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_1999,plain,
% 15.67/2.50      ( m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) = iProver_top
% 15.67/2.50      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 15.67/2.50      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 15.67/2.50      inference(predicate_to_equality,[status(thm)],[c_1998]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_1213,plain,( X0_46 = X0_46 ),theory(equality) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_1924,plain,
% 15.67/2.50      ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
% 15.67/2.50      inference(instantiation,[status(thm)],[c_1213]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_1273,plain,
% 15.67/2.50      ( m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 15.67/2.50      | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top
% 15.67/2.50      | m1_subset_1(k12_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) = iProver_top ),
% 15.67/2.50      inference(predicate_to_equality,[status(thm)],[c_1190]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_1275,plain,
% 15.67/2.50      ( m1_subset_1(k12_lattice3(sK2,sK3,sK3),u1_struct_0(sK2)) = iProver_top
% 15.67/2.50      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 15.67/2.50      inference(instantiation,[status(thm)],[c_1273]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_22,negated_conjecture,
% 15.67/2.50      ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
% 15.67/2.50      inference(cnf_transformation,[],[f78]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_1211,negated_conjecture,
% 15.67/2.50      ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
% 15.67/2.50      inference(subtyping,[status(esa)],[c_22]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_1224,plain,
% 15.67/2.50      ( sK3 = sK3 ),
% 15.67/2.50      inference(instantiation,[status(thm)],[c_1213]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_36,plain,
% 15.67/2.50      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 15.67/2.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(c_35,plain,
% 15.67/2.50      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 15.67/2.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 15.67/2.50  
% 15.67/2.50  cnf(contradiction,plain,
% 15.67/2.50      ( $false ),
% 15.67/2.50      inference(minisat,
% 15.67/2.50                [status(thm)],
% 15.67/2.50                [c_38626,c_9535,c_9527,c_4994,c_2332,c_2327,c_2276,
% 15.67/2.50                 c_2275,c_1999,c_1998,c_1924,c_1275,c_1211,c_1224,c_36,
% 15.67/2.50                 c_23,c_35,c_24]) ).
% 15.67/2.50  
% 15.67/2.50  
% 15.67/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 15.67/2.50  
% 15.67/2.50  ------                               Statistics
% 15.67/2.50  
% 15.67/2.50  ------ General
% 15.67/2.50  
% 15.67/2.50  abstr_ref_over_cycles:                  0
% 15.67/2.50  abstr_ref_under_cycles:                 0
% 15.67/2.50  gc_basic_clause_elim:                   0
% 15.67/2.50  forced_gc_time:                         0
% 15.67/2.50  parsing_time:                           0.014
% 15.67/2.50  unif_index_cands_time:                  0.
% 15.67/2.50  unif_index_add_time:                    0.
% 15.67/2.50  orderings_time:                         0.
% 15.67/2.50  out_proof_time:                         0.017
% 15.67/2.50  total_time:                             1.845
% 15.67/2.50  num_of_symbols:                         49
% 15.67/2.50  num_of_terms:                           75673
% 15.67/2.50  
% 15.67/2.50  ------ Preprocessing
% 15.67/2.50  
% 15.67/2.50  num_of_splits:                          0
% 15.67/2.50  num_of_split_atoms:                     0
% 15.67/2.50  num_of_reused_defs:                     0
% 15.67/2.50  num_eq_ax_congr_red:                    45
% 15.67/2.50  num_of_sem_filtered_clauses:            3
% 15.67/2.50  num_of_subtypes:                        3
% 15.67/2.50  monotx_restored_types:                  0
% 15.67/2.50  sat_num_of_epr_types:                   0
% 15.67/2.50  sat_num_of_non_cyclic_types:            0
% 15.67/2.50  sat_guarded_non_collapsed_types:        1
% 15.67/2.50  num_pure_diseq_elim:                    0
% 15.67/2.50  simp_replaced_by:                       0
% 15.67/2.50  res_preprocessed:                       112
% 15.67/2.50  prep_upred:                             0
% 15.67/2.50  prep_unflattend:                        20
% 15.67/2.50  smt_new_axioms:                         0
% 15.67/2.50  pred_elim_cands:                        2
% 15.67/2.50  pred_elim:                              5
% 15.67/2.50  pred_elim_cl:                           5
% 15.67/2.50  pred_elim_cycles:                       7
% 15.67/2.50  merged_defs:                            0
% 15.67/2.50  merged_defs_ncl:                        0
% 15.67/2.50  bin_hyper_res:                          0
% 15.67/2.50  prep_cycles:                            4
% 15.67/2.50  pred_elim_time:                         0.014
% 15.67/2.50  splitting_time:                         0.
% 15.67/2.50  sem_filter_time:                        0.
% 15.67/2.50  monotx_time:                            0.
% 15.67/2.50  subtype_inf_time:                       0.
% 15.67/2.50  
% 15.67/2.50  ------ Problem properties
% 15.67/2.50  
% 15.67/2.50  clauses:                                23
% 15.67/2.50  conjectures:                            3
% 15.67/2.50  epr:                                    0
% 15.67/2.50  horn:                                   17
% 15.67/2.50  ground:                                 3
% 15.67/2.50  unary:                                  3
% 15.67/2.50  binary:                                 0
% 15.67/2.50  lits:                                   107
% 15.67/2.50  lits_eq:                                13
% 15.67/2.50  fd_pure:                                0
% 15.67/2.50  fd_pseudo:                              0
% 15.67/2.50  fd_cond:                                0
% 15.67/2.50  fd_pseudo_cond:                         8
% 15.67/2.50  ac_symbols:                             0
% 15.67/2.50  
% 15.67/2.50  ------ Propositional Solver
% 15.67/2.50  
% 15.67/2.50  prop_solver_calls:                      32
% 15.67/2.50  prop_fast_solver_calls:                 1864
% 15.67/2.50  smt_solver_calls:                       0
% 15.67/2.50  smt_fast_solver_calls:                  0
% 15.67/2.50  prop_num_of_clauses:                    15052
% 15.67/2.50  prop_preprocess_simplified:             43047
% 15.67/2.50  prop_fo_subsumed:                       64
% 15.67/2.50  prop_solver_time:                       0.
% 15.67/2.50  smt_solver_time:                        0.
% 15.67/2.50  smt_fast_solver_time:                   0.
% 15.67/2.50  prop_fast_solver_time:                  0.
% 15.67/2.50  prop_unsat_core_time:                   0.001
% 15.67/2.50  
% 15.67/2.50  ------ QBF
% 15.67/2.50  
% 15.67/2.50  qbf_q_res:                              0
% 15.67/2.50  qbf_num_tautologies:                    0
% 15.67/2.50  qbf_prep_cycles:                        0
% 15.67/2.50  
% 15.67/2.50  ------ BMC1
% 15.67/2.50  
% 15.67/2.50  bmc1_current_bound:                     -1
% 15.67/2.50  bmc1_last_solved_bound:                 -1
% 15.67/2.50  bmc1_unsat_core_size:                   -1
% 15.67/2.50  bmc1_unsat_core_parents_size:           -1
% 15.67/2.50  bmc1_merge_next_fun:                    0
% 15.67/2.50  bmc1_unsat_core_clauses_time:           0.
% 15.67/2.50  
% 15.67/2.50  ------ Instantiation
% 15.67/2.50  
% 15.67/2.50  inst_num_of_clauses:                    4790
% 15.67/2.50  inst_num_in_passive:                    3630
% 15.67/2.50  inst_num_in_active:                     737
% 15.67/2.50  inst_num_in_unprocessed:                423
% 15.67/2.50  inst_num_of_loops:                      950
% 15.67/2.50  inst_num_of_learning_restarts:          0
% 15.67/2.50  inst_num_moves_active_passive:          210
% 15.67/2.50  inst_lit_activity:                      0
% 15.67/2.50  inst_lit_activity_moves:                1
% 15.67/2.50  inst_num_tautologies:                   0
% 15.67/2.50  inst_num_prop_implied:                  0
% 15.67/2.50  inst_num_existing_simplified:           0
% 15.67/2.50  inst_num_eq_res_simplified:             0
% 15.67/2.50  inst_num_child_elim:                    0
% 15.67/2.50  inst_num_of_dismatching_blockings:      3032
% 15.67/2.50  inst_num_of_non_proper_insts:           3772
% 15.67/2.50  inst_num_of_duplicates:                 0
% 15.67/2.50  inst_inst_num_from_inst_to_res:         0
% 15.67/2.50  inst_dismatching_checking_time:         0.
% 15.67/2.50  
% 15.67/2.50  ------ Resolution
% 15.67/2.50  
% 15.67/2.50  res_num_of_clauses:                     0
% 15.67/2.50  res_num_in_passive:                     0
% 15.67/2.50  res_num_in_active:                      0
% 15.67/2.50  res_num_of_loops:                       116
% 15.67/2.50  res_forward_subset_subsumed:            90
% 15.67/2.50  res_backward_subset_subsumed:           0
% 15.67/2.50  res_forward_subsumed:                   0
% 15.67/2.50  res_backward_subsumed:                  0
% 15.67/2.50  res_forward_subsumption_resolution:     0
% 15.67/2.50  res_backward_subsumption_resolution:    0
% 15.67/2.50  res_clause_to_clause_subsumption:       3853
% 15.67/2.50  res_orphan_elimination:                 0
% 15.67/2.50  res_tautology_del:                      79
% 15.67/2.50  res_num_eq_res_simplified:              0
% 15.67/2.50  res_num_sel_changes:                    0
% 15.67/2.50  res_moves_from_active_to_pass:          0
% 15.67/2.50  
% 15.67/2.50  ------ Superposition
% 15.67/2.50  
% 15.67/2.50  sup_time_total:                         0.
% 15.67/2.50  sup_time_generating:                    0.
% 15.67/2.50  sup_time_sim_full:                      0.
% 15.67/2.50  sup_time_sim_immed:                     0.
% 15.67/2.50  
% 15.67/2.50  sup_num_of_clauses:                     668
% 15.67/2.50  sup_num_in_active:                      184
% 15.67/2.50  sup_num_in_passive:                     484
% 15.67/2.50  sup_num_of_loops:                       189
% 15.67/2.50  sup_fw_superposition:                   461
% 15.67/2.50  sup_bw_superposition:                   225
% 15.67/2.50  sup_immediate_simplified:               205
% 15.67/2.50  sup_given_eliminated:                   0
% 15.67/2.50  comparisons_done:                       0
% 15.67/2.50  comparisons_avoided:                    0
% 15.67/2.50  
% 15.67/2.50  ------ Simplifications
% 15.67/2.50  
% 15.67/2.50  
% 15.67/2.50  sim_fw_subset_subsumed:                 9
% 15.67/2.50  sim_bw_subset_subsumed:                 4
% 15.67/2.50  sim_fw_subsumed:                        3
% 15.67/2.50  sim_bw_subsumed:                        0
% 15.67/2.50  sim_fw_subsumption_res:                 0
% 15.67/2.50  sim_bw_subsumption_res:                 0
% 15.67/2.50  sim_tautology_del:                      6
% 15.67/2.50  sim_eq_tautology_del:                   2
% 15.67/2.50  sim_eq_res_simp:                        0
% 15.67/2.50  sim_fw_demodulated:                     2
% 15.67/2.50  sim_bw_demodulated:                     4
% 15.67/2.50  sim_light_normalised:                   191
% 15.67/2.50  sim_joinable_taut:                      0
% 15.67/2.50  sim_joinable_simp:                      0
% 15.67/2.50  sim_ac_normalised:                      0
% 15.67/2.50  sim_smt_subsumption:                    0
% 15.67/2.50  
%------------------------------------------------------------------------------
