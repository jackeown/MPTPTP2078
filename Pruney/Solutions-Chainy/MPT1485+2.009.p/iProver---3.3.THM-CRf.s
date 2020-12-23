%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:04 EST 2020

% Result     : Theorem 11.61s
% Output     : CNFRefutation 11.61s
% Verified   : 
% Statistics : Number of formulae       :  188 (1721 expanded)
%              Number of clauses        :  120 ( 446 expanded)
%              Number of leaves         :   18 ( 541 expanded)
%              Depth                    :   21
%              Number of atoms          : 1045 (10860 expanded)
%              Number of equality atoms :  232 (1861 expanded)
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

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f74,plain,(
    v2_lattice3(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f72,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f75,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

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

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

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
    inference(nnf_transformation,[],[f22])).

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
    inference(equality_resolution,[],[f53])).

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
    inference(ennf_transformation,[],[f6])).

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
    inference(flattening,[],[f23])).

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
    inference(nnf_transformation,[],[f24])).

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
    inference(cnf_transformation,[],[f44])).

fof(f77,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f48])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

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

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k12_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_26,negated_conjecture,
    ( v2_lattice3(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_636,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k12_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_26])).

cnf(c_637,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(k12_lattice3(sK2,X0,X1),u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_636])).

cnf(c_28,negated_conjecture,
    ( v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_25,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_641,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(k12_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_637,c_28,c_25])).

cnf(c_1199,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | m1_subset_1(k12_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_641])).

cnf(c_1602,plain,
    ( m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k12_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1199])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_27,negated_conjecture,
    ( v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_941,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_27])).

cnf(c_942,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k10_lattice3(sK2,X0,X1) = k13_lattice3(sK2,X0,X1) ),
    inference(unflattening,[status(thm)],[c_941])).

cnf(c_946,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k10_lattice3(sK2,X0,X1) = k13_lattice3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_942,c_28,c_25])).

cnf(c_1190,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | k10_lattice3(sK2,X0_46,X1_46) = k13_lattice3(sK2,X0_46,X1_46) ),
    inference(subtyping,[status(esa)],[c_946])).

cnf(c_1611,plain,
    ( k10_lattice3(sK2,X0_46,X1_46) = k13_lattice3(sK2,X0_46,X1_46)
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1190])).

cnf(c_5215,plain,
    ( k10_lattice3(sK2,k12_lattice3(sK2,X0_46,X1_46),X2_46) = k13_lattice3(sK2,k12_lattice3(sK2,X0_46,X1_46),X2_46)
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_46,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1602,c_1611])).

cnf(c_29828,plain,
    ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,X0_46),X1_46) = k13_lattice3(sK2,k12_lattice3(sK2,sK3,X0_46),X1_46)
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1592,c_5215])).

cnf(c_30708,plain,
    ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK3),X0_46) = k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK3),X0_46)
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1592,c_29828])).

cnf(c_31395,plain,
    ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK3),sK3) = k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK3),sK3) ),
    inference(superposition,[status(thm)],[c_1592,c_30708])).

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

cnf(c_1991,plain,
    ( k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK3),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_1592,c_1883])).

cnf(c_5214,plain,
    ( k10_lattice3(sK2,sK3,X0_46) = k13_lattice3(sK2,sK3,X0_46)
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1592,c_1611])).

cnf(c_5872,plain,
    ( k10_lattice3(sK2,sK3,k12_lattice3(sK2,X0_46,X1_46)) = k13_lattice3(sK2,sK3,k12_lattice3(sK2,X0_46,X1_46))
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1602,c_5214])).

cnf(c_21114,plain,
    ( k10_lattice3(sK2,sK3,k12_lattice3(sK2,sK3,X0_46)) = k13_lattice3(sK2,sK3,k12_lattice3(sK2,sK3,X0_46))
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1592,c_5872])).

cnf(c_22115,plain,
    ( k10_lattice3(sK2,sK3,k12_lattice3(sK2,sK3,sK3)) = k13_lattice3(sK2,sK3,k12_lattice3(sK2,sK3,sK3)) ),
    inference(superposition,[status(thm)],[c_1592,c_21114])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | k10_lattice3(X1,X0,X2) = k10_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_920,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k10_lattice3(X1,X0,X2) = k10_lattice3(X1,X2,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_921,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k10_lattice3(sK2,X1,X0) = k10_lattice3(sK2,X0,X1) ),
    inference(unflattening,[status(thm)],[c_920])).

cnf(c_925,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k10_lattice3(sK2,X1,X0) = k10_lattice3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_921,c_28,c_25])).

cnf(c_1191,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | k10_lattice3(sK2,X1_46,X0_46) = k10_lattice3(sK2,X0_46,X1_46) ),
    inference(subtyping,[status(esa)],[c_925])).

cnf(c_1610,plain,
    ( k10_lattice3(sK2,X0_46,X1_46) = k10_lattice3(sK2,X1_46,X0_46)
    | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1191])).

cnf(c_3810,plain,
    ( k10_lattice3(sK2,X0_46,sK3) = k10_lattice3(sK2,sK3,X0_46)
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1592,c_1610])).

cnf(c_4082,plain,
    ( k10_lattice3(sK2,sK3,k12_lattice3(sK2,X0_46,X1_46)) = k10_lattice3(sK2,k12_lattice3(sK2,X0_46,X1_46),sK3)
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1602,c_3810])).

cnf(c_16904,plain,
    ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,X0_46),sK3) = k10_lattice3(sK2,sK3,k12_lattice3(sK2,sK3,X0_46))
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1592,c_4082])).

cnf(c_17708,plain,
    ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK3),sK3) = k10_lattice3(sK2,sK3,k12_lattice3(sK2,sK3,sK3)) ),
    inference(superposition,[status(thm)],[c_1592,c_16904])).

cnf(c_23381,plain,
    ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK3),sK3) = k13_lattice3(sK2,sK3,k12_lattice3(sK2,sK3,sK3)) ),
    inference(demodulation,[status(thm)],[c_22115,c_17708])).

cnf(c_31441,plain,
    ( k13_lattice3(sK2,sK3,k12_lattice3(sK2,sK3,sK3)) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_31395,c_1991,c_23381])).

cnf(c_32108,plain,
    ( k10_lattice3(sK2,sK3,k12_lattice3(sK2,sK3,sK3)) = sK3 ),
    inference(demodulation,[status(thm)],[c_31441,c_22115])).

cnf(c_10,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_210,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_0])).

cnf(c_211,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0) ),
    inference(renaming,[status(thm)],[c_210])).

cnf(c_900,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_211,c_27])).

cnf(c_901,plain,
    ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_900])).

cnf(c_903,plain,
    ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_901,c_28,c_25])).

cnf(c_904,plain,
    ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_903])).

cnf(c_1192,plain,
    ( r1_orders_2(sK2,X0_46,k10_lattice3(sK2,X0_46,X1_46))
    | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_904])).

cnf(c_1609,plain,
    ( r1_orders_2(sK2,X0_46,k10_lattice3(sK2,X0_46,X1_46)) = iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k10_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1192])).

cnf(c_33424,plain,
    ( r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,k12_lattice3(sK2,sK3,sK3))) = iProver_top
    | m1_subset_1(k12_lattice3(sK2,sK3,sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_32108,c_1609])).

cnf(c_33441,plain,
    ( r1_orders_2(sK2,sK3,sK3) = iProver_top
    | m1_subset_1(k12_lattice3(sK2,sK3,sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_33424,c_32108])).

cnf(c_11,plain,
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
    inference(cnf_transformation,[],[f66])).

cnf(c_1,plain,
    ( ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_203,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_1])).

cnf(c_204,plain,
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
    inference(renaming,[status(thm)],[c_203])).

cnf(c_410,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK1(X0,X3,X2,X1),X1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_204,c_26])).

cnf(c_411,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | ~ r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X0)
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k11_lattice3(sK2,X1,X2) = X0 ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_415,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | ~ r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X0)
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k11_lattice3(sK2,X1,X2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_411,c_28,c_25])).

cnf(c_1207,plain,
    ( ~ r1_orders_2(sK2,X0_46,X1_46)
    | ~ r1_orders_2(sK2,X0_46,X2_46)
    | ~ r1_orders_2(sK2,sK1(sK2,X1_46,X2_46,X0_46),X0_46)
    | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X2_46,u1_struct_0(sK2))
    | k11_lattice3(sK2,X1_46,X2_46) = X0_46 ),
    inference(subtyping,[status(esa)],[c_415])).

cnf(c_32589,plain,
    ( ~ r1_orders_2(sK2,X0_46,k13_lattice3(sK2,sK3,sK4))
    | ~ r1_orders_2(sK2,X0_46,sK3)
    | ~ r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_46),X0_46)
    | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46 ),
    inference(instantiation,[status(thm)],[c_1207])).

cnf(c_32605,plain,
    ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46
    | r1_orders_2(sK2,X0_46,k13_lattice3(sK2,sK3,sK4)) != iProver_top
    | r1_orders_2(sK2,X0_46,sK3) != iProver_top
    | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_46),X0_46) != iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32589])).

cnf(c_32607,plain,
    ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
    | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),sK3),sK3) != iProver_top
    | r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != iProver_top
    | r1_orders_2(sK2,sK3,sK3) != iProver_top
    | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_32605])).

cnf(c_13,plain,
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
    inference(cnf_transformation,[],[f64])).

cnf(c_191,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_1])).

cnf(c_192,plain,
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
    inference(renaming,[status(thm)],[c_191])).

cnf(c_476,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK1(X0,X3,X2,X1),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_192,c_26])).

cnf(c_477,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k11_lattice3(sK2,X1,X2) = X0 ),
    inference(unflattening,[status(thm)],[c_476])).

cnf(c_479,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k11_lattice3(sK2,X1,X2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_477,c_28,c_25])).

cnf(c_1205,plain,
    ( ~ r1_orders_2(sK2,X0_46,X1_46)
    | ~ r1_orders_2(sK2,X0_46,X2_46)
    | r1_orders_2(sK2,sK1(sK2,X1_46,X2_46,X0_46),X1_46)
    | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X2_46,u1_struct_0(sK2))
    | k11_lattice3(sK2,X1_46,X2_46) = X0_46 ),
    inference(subtyping,[status(esa)],[c_479])).

cnf(c_32591,plain,
    ( ~ r1_orders_2(sK2,X0_46,k13_lattice3(sK2,sK3,sK4))
    | ~ r1_orders_2(sK2,X0_46,sK3)
    | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_46),sK3)
    | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46 ),
    inference(instantiation,[status(thm)],[c_1205])).

cnf(c_32597,plain,
    ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46
    | r1_orders_2(sK2,X0_46,k13_lattice3(sK2,sK3,sK4)) != iProver_top
    | r1_orders_2(sK2,X0_46,sK3) != iProver_top
    | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_46),sK3) = iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32591])).

cnf(c_32599,plain,
    ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
    | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),sK3),sK3) = iProver_top
    | r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != iProver_top
    | r1_orders_2(sK2,sK3,sK3) != iProver_top
    | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_32597])).

cnf(c_1214,plain,
    ( X0_46 != X1_46
    | X2_46 != X1_46
    | X2_46 = X0_46 ),
    theory(equality)).

cnf(c_2479,plain,
    ( X0_46 != X1_46
    | X0_46 = k11_lattice3(sK2,X2_46,X3_46)
    | k11_lattice3(sK2,X2_46,X3_46) != X1_46 ),
    inference(instantiation,[status(thm)],[c_1214])).

cnf(c_11339,plain,
    ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != X0_46
    | sK3 != X0_46
    | sK3 = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2479])).

cnf(c_11340,plain,
    ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3
    | sK3 = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_11339])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1210,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1591,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1210])).

cnf(c_5870,plain,
    ( k10_lattice3(sK2,sK3,sK4) = k13_lattice3(sK2,sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1591,c_5214])).

cnf(c_7162,plain,
    ( r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK4)) = iProver_top
    | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5870,c_1609])).

cnf(c_7178,plain,
    ( r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = iProver_top
    | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7162,c_5870])).

cnf(c_1896,plain,
    ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != X0_46
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
    | sK3 != X0_46 ),
    inference(instantiation,[status(thm)],[c_1214])).

cnf(c_7024,plain,
    ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
    | sK3 != k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1896])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k13_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_962,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k13_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_27])).

cnf(c_963,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(k13_lattice3(sK2,X0,X1),u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_962])).

cnf(c_967,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(k13_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_963,c_28,c_25])).

cnf(c_1189,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | m1_subset_1(k13_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_967])).

cnf(c_5027,plain,
    ( m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1189])).

cnf(c_5028,plain,
    ( m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5027])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_615,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_26])).

cnf(c_616,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k11_lattice3(sK2,X0,X1) = k12_lattice3(sK2,X0,X1) ),
    inference(unflattening,[status(thm)],[c_615])).

cnf(c_620,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k11_lattice3(sK2,X0,X1) = k12_lattice3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_616,c_28,c_25])).

cnf(c_1200,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | k11_lattice3(sK2,X0_46,X1_46) = k12_lattice3(sK2,X0_46,X1_46) ),
    inference(subtyping,[status(esa)],[c_620])).

cnf(c_4468,plain,
    ( ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1200])).

cnf(c_1921,plain,
    ( X0_46 != X1_46
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != X1_46
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46 ),
    inference(instantiation,[status(thm)],[c_1214])).

cnf(c_1983,plain,
    ( X0_46 != k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1921])).

cnf(c_4467,plain,
    ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1983])).

cnf(c_1213,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_1920,plain,
    ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1213])).

cnf(c_1250,plain,
    ( m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k12_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1199])).

cnf(c_1252,plain,
    ( m1_subset_1(k12_lattice3(sK2,sK3,sK3),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1250])).

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
    inference(minisat,[status(thm)],[c_33441,c_32607,c_32599,c_11340,c_7178,c_7024,c_5028,c_5027,c_4468,c_4467,c_1920,c_1252,c_1211,c_1224,c_36,c_23,c_35,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:28:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 11.61/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.61/1.99  
% 11.61/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.61/1.99  
% 11.61/1.99  ------  iProver source info
% 11.61/1.99  
% 11.61/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.61/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.61/1.99  git: non_committed_changes: false
% 11.61/1.99  git: last_make_outside_of_git: false
% 11.61/1.99  
% 11.61/1.99  ------ 
% 11.61/1.99  
% 11.61/1.99  ------ Input Options
% 11.61/1.99  
% 11.61/1.99  --out_options                           all
% 11.61/1.99  --tptp_safe_out                         true
% 11.61/1.99  --problem_path                          ""
% 11.61/1.99  --include_path                          ""
% 11.61/1.99  --clausifier                            res/vclausify_rel
% 11.61/1.99  --clausifier_options                    --mode clausify
% 11.61/1.99  --stdin                                 false
% 11.61/1.99  --stats_out                             all
% 11.61/1.99  
% 11.61/1.99  ------ General Options
% 11.61/1.99  
% 11.61/1.99  --fof                                   false
% 11.61/1.99  --time_out_real                         305.
% 11.61/1.99  --time_out_virtual                      -1.
% 11.61/1.99  --symbol_type_check                     false
% 11.61/1.99  --clausify_out                          false
% 11.61/1.99  --sig_cnt_out                           false
% 11.61/1.99  --trig_cnt_out                          false
% 11.61/1.99  --trig_cnt_out_tolerance                1.
% 11.61/1.99  --trig_cnt_out_sk_spl                   false
% 11.61/1.99  --abstr_cl_out                          false
% 11.61/1.99  
% 11.61/1.99  ------ Global Options
% 11.61/1.99  
% 11.61/1.99  --schedule                              default
% 11.61/1.99  --add_important_lit                     false
% 11.61/1.99  --prop_solver_per_cl                    1000
% 11.61/1.99  --min_unsat_core                        false
% 11.61/1.99  --soft_assumptions                      false
% 11.61/1.99  --soft_lemma_size                       3
% 11.61/1.99  --prop_impl_unit_size                   0
% 11.61/1.99  --prop_impl_unit                        []
% 11.61/1.99  --share_sel_clauses                     true
% 11.61/1.99  --reset_solvers                         false
% 11.61/1.99  --bc_imp_inh                            [conj_cone]
% 11.61/1.99  --conj_cone_tolerance                   3.
% 11.61/1.99  --extra_neg_conj                        none
% 11.61/1.99  --large_theory_mode                     true
% 11.61/1.99  --prolific_symb_bound                   200
% 11.61/1.99  --lt_threshold                          2000
% 11.61/1.99  --clause_weak_htbl                      true
% 11.61/1.99  --gc_record_bc_elim                     false
% 11.61/1.99  
% 11.61/1.99  ------ Preprocessing Options
% 11.61/1.99  
% 11.61/1.99  --preprocessing_flag                    true
% 11.61/1.99  --time_out_prep_mult                    0.1
% 11.61/1.99  --splitting_mode                        input
% 11.61/1.99  --splitting_grd                         true
% 11.61/1.99  --splitting_cvd                         false
% 11.61/1.99  --splitting_cvd_svl                     false
% 11.61/1.99  --splitting_nvd                         32
% 11.61/1.99  --sub_typing                            true
% 11.61/1.99  --prep_gs_sim                           true
% 11.61/1.99  --prep_unflatten                        true
% 11.61/1.99  --prep_res_sim                          true
% 11.61/1.99  --prep_upred                            true
% 11.61/1.99  --prep_sem_filter                       exhaustive
% 11.61/1.99  --prep_sem_filter_out                   false
% 11.61/1.99  --pred_elim                             true
% 11.61/1.99  --res_sim_input                         true
% 11.61/1.99  --eq_ax_congr_red                       true
% 11.61/1.99  --pure_diseq_elim                       true
% 11.61/1.99  --brand_transform                       false
% 11.61/1.99  --non_eq_to_eq                          false
% 11.61/1.99  --prep_def_merge                        true
% 11.61/1.99  --prep_def_merge_prop_impl              false
% 11.61/1.99  --prep_def_merge_mbd                    true
% 11.61/1.99  --prep_def_merge_tr_red                 false
% 11.61/1.99  --prep_def_merge_tr_cl                  false
% 11.61/1.99  --smt_preprocessing                     true
% 11.61/1.99  --smt_ac_axioms                         fast
% 11.61/1.99  --preprocessed_out                      false
% 11.61/1.99  --preprocessed_stats                    false
% 11.61/1.99  
% 11.61/1.99  ------ Abstraction refinement Options
% 11.61/1.99  
% 11.61/1.99  --abstr_ref                             []
% 11.61/1.99  --abstr_ref_prep                        false
% 11.61/1.99  --abstr_ref_until_sat                   false
% 11.61/1.99  --abstr_ref_sig_restrict                funpre
% 11.61/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.61/1.99  --abstr_ref_under                       []
% 11.61/1.99  
% 11.61/1.99  ------ SAT Options
% 11.61/1.99  
% 11.61/1.99  --sat_mode                              false
% 11.61/1.99  --sat_fm_restart_options                ""
% 11.61/1.99  --sat_gr_def                            false
% 11.61/1.99  --sat_epr_types                         true
% 11.61/1.99  --sat_non_cyclic_types                  false
% 11.61/1.99  --sat_finite_models                     false
% 11.61/1.99  --sat_fm_lemmas                         false
% 11.61/1.99  --sat_fm_prep                           false
% 11.61/1.99  --sat_fm_uc_incr                        true
% 11.61/1.99  --sat_out_model                         small
% 11.61/1.99  --sat_out_clauses                       false
% 11.61/1.99  
% 11.61/1.99  ------ QBF Options
% 11.61/1.99  
% 11.61/1.99  --qbf_mode                              false
% 11.61/1.99  --qbf_elim_univ                         false
% 11.61/1.99  --qbf_dom_inst                          none
% 11.61/1.99  --qbf_dom_pre_inst                      false
% 11.61/1.99  --qbf_sk_in                             false
% 11.61/1.99  --qbf_pred_elim                         true
% 11.61/1.99  --qbf_split                             512
% 11.61/1.99  
% 11.61/1.99  ------ BMC1 Options
% 11.61/1.99  
% 11.61/1.99  --bmc1_incremental                      false
% 11.61/1.99  --bmc1_axioms                           reachable_all
% 11.61/1.99  --bmc1_min_bound                        0
% 11.61/1.99  --bmc1_max_bound                        -1
% 11.61/1.99  --bmc1_max_bound_default                -1
% 11.61/1.99  --bmc1_symbol_reachability              true
% 11.61/1.99  --bmc1_property_lemmas                  false
% 11.61/1.99  --bmc1_k_induction                      false
% 11.61/1.99  --bmc1_non_equiv_states                 false
% 11.61/1.99  --bmc1_deadlock                         false
% 11.61/1.99  --bmc1_ucm                              false
% 11.61/1.99  --bmc1_add_unsat_core                   none
% 11.61/1.99  --bmc1_unsat_core_children              false
% 11.61/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.61/1.99  --bmc1_out_stat                         full
% 11.61/1.99  --bmc1_ground_init                      false
% 11.61/1.99  --bmc1_pre_inst_next_state              false
% 11.61/1.99  --bmc1_pre_inst_state                   false
% 11.61/1.99  --bmc1_pre_inst_reach_state             false
% 11.61/1.99  --bmc1_out_unsat_core                   false
% 11.61/1.99  --bmc1_aig_witness_out                  false
% 11.61/1.99  --bmc1_verbose                          false
% 11.61/1.99  --bmc1_dump_clauses_tptp                false
% 11.61/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.61/1.99  --bmc1_dump_file                        -
% 11.61/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.61/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.61/1.99  --bmc1_ucm_extend_mode                  1
% 11.61/1.99  --bmc1_ucm_init_mode                    2
% 11.61/1.99  --bmc1_ucm_cone_mode                    none
% 11.61/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.61/1.99  --bmc1_ucm_relax_model                  4
% 11.61/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.61/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.61/1.99  --bmc1_ucm_layered_model                none
% 11.61/1.99  --bmc1_ucm_max_lemma_size               10
% 11.61/1.99  
% 11.61/1.99  ------ AIG Options
% 11.61/1.99  
% 11.61/1.99  --aig_mode                              false
% 11.61/1.99  
% 11.61/1.99  ------ Instantiation Options
% 11.61/1.99  
% 11.61/1.99  --instantiation_flag                    true
% 11.61/1.99  --inst_sos_flag                         false
% 11.61/1.99  --inst_sos_phase                        true
% 11.61/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.61/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.61/1.99  --inst_lit_sel_side                     num_symb
% 11.61/1.99  --inst_solver_per_active                1400
% 11.61/1.99  --inst_solver_calls_frac                1.
% 11.61/1.99  --inst_passive_queue_type               priority_queues
% 11.61/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.61/1.99  --inst_passive_queues_freq              [25;2]
% 11.61/1.99  --inst_dismatching                      true
% 11.61/1.99  --inst_eager_unprocessed_to_passive     true
% 11.61/1.99  --inst_prop_sim_given                   true
% 11.61/1.99  --inst_prop_sim_new                     false
% 11.61/1.99  --inst_subs_new                         false
% 11.61/1.99  --inst_eq_res_simp                      false
% 11.61/1.99  --inst_subs_given                       false
% 11.61/1.99  --inst_orphan_elimination               true
% 11.61/1.99  --inst_learning_loop_flag               true
% 11.61/1.99  --inst_learning_start                   3000
% 11.61/1.99  --inst_learning_factor                  2
% 11.61/1.99  --inst_start_prop_sim_after_learn       3
% 11.61/1.99  --inst_sel_renew                        solver
% 11.61/1.99  --inst_lit_activity_flag                true
% 11.61/1.99  --inst_restr_to_given                   false
% 11.61/1.99  --inst_activity_threshold               500
% 11.61/1.99  --inst_out_proof                        true
% 11.61/1.99  
% 11.61/1.99  ------ Resolution Options
% 11.61/1.99  
% 11.61/1.99  --resolution_flag                       true
% 11.61/1.99  --res_lit_sel                           adaptive
% 11.61/1.99  --res_lit_sel_side                      none
% 11.61/1.99  --res_ordering                          kbo
% 11.61/1.99  --res_to_prop_solver                    active
% 11.61/1.99  --res_prop_simpl_new                    false
% 11.61/1.99  --res_prop_simpl_given                  true
% 11.61/1.99  --res_passive_queue_type                priority_queues
% 11.61/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.61/1.99  --res_passive_queues_freq               [15;5]
% 11.61/1.99  --res_forward_subs                      full
% 11.61/1.99  --res_backward_subs                     full
% 11.61/1.99  --res_forward_subs_resolution           true
% 11.61/1.99  --res_backward_subs_resolution          true
% 11.61/1.99  --res_orphan_elimination                true
% 11.61/1.99  --res_time_limit                        2.
% 11.61/1.99  --res_out_proof                         true
% 11.61/1.99  
% 11.61/1.99  ------ Superposition Options
% 11.61/1.99  
% 11.61/1.99  --superposition_flag                    true
% 11.61/1.99  --sup_passive_queue_type                priority_queues
% 11.61/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.61/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.61/1.99  --demod_completeness_check              fast
% 11.61/1.99  --demod_use_ground                      true
% 11.61/1.99  --sup_to_prop_solver                    passive
% 11.61/1.99  --sup_prop_simpl_new                    true
% 11.61/1.99  --sup_prop_simpl_given                  true
% 11.61/1.99  --sup_fun_splitting                     false
% 11.61/1.99  --sup_smt_interval                      50000
% 11.61/1.99  
% 11.61/1.99  ------ Superposition Simplification Setup
% 11.61/1.99  
% 11.61/1.99  --sup_indices_passive                   []
% 11.61/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.61/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.61/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.61/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.61/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.61/1.99  --sup_full_bw                           [BwDemod]
% 11.61/1.99  --sup_immed_triv                        [TrivRules]
% 11.61/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.61/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.61/1.99  --sup_immed_bw_main                     []
% 11.61/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.61/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.61/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.61/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.61/1.99  
% 11.61/1.99  ------ Combination Options
% 11.61/1.99  
% 11.61/1.99  --comb_res_mult                         3
% 11.61/1.99  --comb_sup_mult                         2
% 11.61/1.99  --comb_inst_mult                        10
% 11.61/1.99  
% 11.61/1.99  ------ Debug Options
% 11.61/1.99  
% 11.61/1.99  --dbg_backtrace                         false
% 11.61/1.99  --dbg_dump_prop_clauses                 false
% 11.61/1.99  --dbg_dump_prop_clauses_file            -
% 11.61/1.99  --dbg_out_stat                          false
% 11.61/1.99  ------ Parsing...
% 11.61/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.61/1.99  
% 11.61/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 11.61/1.99  
% 11.61/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.61/1.99  
% 11.61/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.61/1.99  ------ Proving...
% 11.61/1.99  ------ Problem Properties 
% 11.61/1.99  
% 11.61/1.99  
% 11.61/1.99  clauses                                 23
% 11.61/1.99  conjectures                             3
% 11.61/1.99  EPR                                     0
% 11.61/1.99  Horn                                    17
% 11.61/1.99  unary                                   3
% 11.61/1.99  binary                                  0
% 11.61/1.99  lits                                    107
% 11.61/1.99  lits eq                                 13
% 11.61/1.99  fd_pure                                 0
% 11.61/1.99  fd_pseudo                               0
% 11.61/1.99  fd_cond                                 0
% 11.61/1.99  fd_pseudo_cond                          8
% 11.61/1.99  AC symbols                              0
% 11.61/1.99  
% 11.61/1.99  ------ Schedule dynamic 5 is on 
% 11.61/1.99  
% 11.61/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.61/1.99  
% 11.61/1.99  
% 11.61/1.99  ------ 
% 11.61/1.99  Current options:
% 11.61/1.99  ------ 
% 11.61/1.99  
% 11.61/1.99  ------ Input Options
% 11.61/1.99  
% 11.61/1.99  --out_options                           all
% 11.61/1.99  --tptp_safe_out                         true
% 11.61/1.99  --problem_path                          ""
% 11.61/1.99  --include_path                          ""
% 11.61/1.99  --clausifier                            res/vclausify_rel
% 11.61/1.99  --clausifier_options                    --mode clausify
% 11.61/1.99  --stdin                                 false
% 11.61/1.99  --stats_out                             all
% 11.61/1.99  
% 11.61/1.99  ------ General Options
% 11.61/1.99  
% 11.61/1.99  --fof                                   false
% 11.61/1.99  --time_out_real                         305.
% 11.61/1.99  --time_out_virtual                      -1.
% 11.61/1.99  --symbol_type_check                     false
% 11.61/1.99  --clausify_out                          false
% 11.61/1.99  --sig_cnt_out                           false
% 11.61/1.99  --trig_cnt_out                          false
% 11.61/1.99  --trig_cnt_out_tolerance                1.
% 11.61/1.99  --trig_cnt_out_sk_spl                   false
% 11.61/1.99  --abstr_cl_out                          false
% 11.61/1.99  
% 11.61/1.99  ------ Global Options
% 11.61/1.99  
% 11.61/1.99  --schedule                              default
% 11.61/1.99  --add_important_lit                     false
% 11.61/1.99  --prop_solver_per_cl                    1000
% 11.61/1.99  --min_unsat_core                        false
% 11.61/1.99  --soft_assumptions                      false
% 11.61/1.99  --soft_lemma_size                       3
% 11.61/1.99  --prop_impl_unit_size                   0
% 11.61/1.99  --prop_impl_unit                        []
% 11.61/1.99  --share_sel_clauses                     true
% 11.61/1.99  --reset_solvers                         false
% 11.61/1.99  --bc_imp_inh                            [conj_cone]
% 11.61/1.99  --conj_cone_tolerance                   3.
% 11.61/1.99  --extra_neg_conj                        none
% 11.61/1.99  --large_theory_mode                     true
% 11.61/1.99  --prolific_symb_bound                   200
% 11.61/1.99  --lt_threshold                          2000
% 11.61/1.99  --clause_weak_htbl                      true
% 11.61/1.99  --gc_record_bc_elim                     false
% 11.61/1.99  
% 11.61/1.99  ------ Preprocessing Options
% 11.61/1.99  
% 11.61/1.99  --preprocessing_flag                    true
% 11.61/1.99  --time_out_prep_mult                    0.1
% 11.61/1.99  --splitting_mode                        input
% 11.61/1.99  --splitting_grd                         true
% 11.61/1.99  --splitting_cvd                         false
% 11.61/1.99  --splitting_cvd_svl                     false
% 11.61/1.99  --splitting_nvd                         32
% 11.61/1.99  --sub_typing                            true
% 11.61/1.99  --prep_gs_sim                           true
% 11.61/1.99  --prep_unflatten                        true
% 11.61/1.99  --prep_res_sim                          true
% 11.61/1.99  --prep_upred                            true
% 11.61/1.99  --prep_sem_filter                       exhaustive
% 11.61/1.99  --prep_sem_filter_out                   false
% 11.61/1.99  --pred_elim                             true
% 11.61/1.99  --res_sim_input                         true
% 11.61/1.99  --eq_ax_congr_red                       true
% 11.61/1.99  --pure_diseq_elim                       true
% 11.61/1.99  --brand_transform                       false
% 11.61/1.99  --non_eq_to_eq                          false
% 11.61/1.99  --prep_def_merge                        true
% 11.61/1.99  --prep_def_merge_prop_impl              false
% 11.61/1.99  --prep_def_merge_mbd                    true
% 11.61/1.99  --prep_def_merge_tr_red                 false
% 11.61/1.99  --prep_def_merge_tr_cl                  false
% 11.61/1.99  --smt_preprocessing                     true
% 11.61/1.99  --smt_ac_axioms                         fast
% 11.61/1.99  --preprocessed_out                      false
% 11.61/1.99  --preprocessed_stats                    false
% 11.61/1.99  
% 11.61/1.99  ------ Abstraction refinement Options
% 11.61/1.99  
% 11.61/1.99  --abstr_ref                             []
% 11.61/1.99  --abstr_ref_prep                        false
% 11.61/1.99  --abstr_ref_until_sat                   false
% 11.61/1.99  --abstr_ref_sig_restrict                funpre
% 11.61/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.61/1.99  --abstr_ref_under                       []
% 11.61/1.99  
% 11.61/1.99  ------ SAT Options
% 11.61/1.99  
% 11.61/1.99  --sat_mode                              false
% 11.61/1.99  --sat_fm_restart_options                ""
% 11.61/1.99  --sat_gr_def                            false
% 11.61/1.99  --sat_epr_types                         true
% 11.61/1.99  --sat_non_cyclic_types                  false
% 11.61/1.99  --sat_finite_models                     false
% 11.61/1.99  --sat_fm_lemmas                         false
% 11.61/1.99  --sat_fm_prep                           false
% 11.61/1.99  --sat_fm_uc_incr                        true
% 11.61/1.99  --sat_out_model                         small
% 11.61/1.99  --sat_out_clauses                       false
% 11.61/1.99  
% 11.61/1.99  ------ QBF Options
% 11.61/1.99  
% 11.61/1.99  --qbf_mode                              false
% 11.61/1.99  --qbf_elim_univ                         false
% 11.61/1.99  --qbf_dom_inst                          none
% 11.61/1.99  --qbf_dom_pre_inst                      false
% 11.61/1.99  --qbf_sk_in                             false
% 11.61/1.99  --qbf_pred_elim                         true
% 11.61/1.99  --qbf_split                             512
% 11.61/1.99  
% 11.61/1.99  ------ BMC1 Options
% 11.61/1.99  
% 11.61/1.99  --bmc1_incremental                      false
% 11.61/1.99  --bmc1_axioms                           reachable_all
% 11.61/1.99  --bmc1_min_bound                        0
% 11.61/1.99  --bmc1_max_bound                        -1
% 11.61/1.99  --bmc1_max_bound_default                -1
% 11.61/1.99  --bmc1_symbol_reachability              true
% 11.61/1.99  --bmc1_property_lemmas                  false
% 11.61/1.99  --bmc1_k_induction                      false
% 11.61/1.99  --bmc1_non_equiv_states                 false
% 11.61/1.99  --bmc1_deadlock                         false
% 11.61/1.99  --bmc1_ucm                              false
% 11.61/1.99  --bmc1_add_unsat_core                   none
% 11.61/1.99  --bmc1_unsat_core_children              false
% 11.61/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.61/1.99  --bmc1_out_stat                         full
% 11.61/1.99  --bmc1_ground_init                      false
% 11.61/1.99  --bmc1_pre_inst_next_state              false
% 11.61/1.99  --bmc1_pre_inst_state                   false
% 11.61/1.99  --bmc1_pre_inst_reach_state             false
% 11.61/1.99  --bmc1_out_unsat_core                   false
% 11.61/1.99  --bmc1_aig_witness_out                  false
% 11.61/1.99  --bmc1_verbose                          false
% 11.61/1.99  --bmc1_dump_clauses_tptp                false
% 11.61/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.61/1.99  --bmc1_dump_file                        -
% 11.61/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.61/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.61/1.99  --bmc1_ucm_extend_mode                  1
% 11.61/1.99  --bmc1_ucm_init_mode                    2
% 11.61/1.99  --bmc1_ucm_cone_mode                    none
% 11.61/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.61/1.99  --bmc1_ucm_relax_model                  4
% 11.61/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.61/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.61/1.99  --bmc1_ucm_layered_model                none
% 11.61/1.99  --bmc1_ucm_max_lemma_size               10
% 11.61/1.99  
% 11.61/1.99  ------ AIG Options
% 11.61/1.99  
% 11.61/1.99  --aig_mode                              false
% 11.61/1.99  
% 11.61/1.99  ------ Instantiation Options
% 11.61/1.99  
% 11.61/1.99  --instantiation_flag                    true
% 11.61/1.99  --inst_sos_flag                         false
% 11.61/1.99  --inst_sos_phase                        true
% 11.61/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.61/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.61/1.99  --inst_lit_sel_side                     none
% 11.61/1.99  --inst_solver_per_active                1400
% 11.61/1.99  --inst_solver_calls_frac                1.
% 11.61/1.99  --inst_passive_queue_type               priority_queues
% 11.61/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.61/1.99  --inst_passive_queues_freq              [25;2]
% 11.61/1.99  --inst_dismatching                      true
% 11.61/1.99  --inst_eager_unprocessed_to_passive     true
% 11.61/1.99  --inst_prop_sim_given                   true
% 11.61/1.99  --inst_prop_sim_new                     false
% 11.61/1.99  --inst_subs_new                         false
% 11.61/1.99  --inst_eq_res_simp                      false
% 11.61/1.99  --inst_subs_given                       false
% 11.61/1.99  --inst_orphan_elimination               true
% 11.61/1.99  --inst_learning_loop_flag               true
% 11.61/1.99  --inst_learning_start                   3000
% 11.61/1.99  --inst_learning_factor                  2
% 11.61/1.99  --inst_start_prop_sim_after_learn       3
% 11.61/1.99  --inst_sel_renew                        solver
% 11.61/1.99  --inst_lit_activity_flag                true
% 11.61/1.99  --inst_restr_to_given                   false
% 11.61/1.99  --inst_activity_threshold               500
% 11.61/1.99  --inst_out_proof                        true
% 11.61/1.99  
% 11.61/1.99  ------ Resolution Options
% 11.61/1.99  
% 11.61/1.99  --resolution_flag                       false
% 11.61/1.99  --res_lit_sel                           adaptive
% 11.61/1.99  --res_lit_sel_side                      none
% 11.61/1.99  --res_ordering                          kbo
% 11.61/1.99  --res_to_prop_solver                    active
% 11.61/1.99  --res_prop_simpl_new                    false
% 11.61/1.99  --res_prop_simpl_given                  true
% 11.61/1.99  --res_passive_queue_type                priority_queues
% 11.61/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.61/1.99  --res_passive_queues_freq               [15;5]
% 11.61/1.99  --res_forward_subs                      full
% 11.61/1.99  --res_backward_subs                     full
% 11.61/1.99  --res_forward_subs_resolution           true
% 11.61/1.99  --res_backward_subs_resolution          true
% 11.61/1.99  --res_orphan_elimination                true
% 11.61/1.99  --res_time_limit                        2.
% 11.61/1.99  --res_out_proof                         true
% 11.61/1.99  
% 11.61/1.99  ------ Superposition Options
% 11.61/1.99  
% 11.61/1.99  --superposition_flag                    true
% 11.61/1.99  --sup_passive_queue_type                priority_queues
% 11.61/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.61/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.61/1.99  --demod_completeness_check              fast
% 11.61/1.99  --demod_use_ground                      true
% 11.61/1.99  --sup_to_prop_solver                    passive
% 11.61/1.99  --sup_prop_simpl_new                    true
% 11.61/1.99  --sup_prop_simpl_given                  true
% 11.61/1.99  --sup_fun_splitting                     false
% 11.61/1.99  --sup_smt_interval                      50000
% 11.61/1.99  
% 11.61/1.99  ------ Superposition Simplification Setup
% 11.61/1.99  
% 11.61/1.99  --sup_indices_passive                   []
% 11.61/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.61/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.61/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.61/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.61/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.61/1.99  --sup_full_bw                           [BwDemod]
% 11.61/1.99  --sup_immed_triv                        [TrivRules]
% 11.61/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.61/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.61/1.99  --sup_immed_bw_main                     []
% 11.61/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.61/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.61/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.61/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.61/1.99  
% 11.61/1.99  ------ Combination Options
% 11.61/1.99  
% 11.61/1.99  --comb_res_mult                         3
% 11.61/1.99  --comb_sup_mult                         2
% 11.61/1.99  --comb_inst_mult                        10
% 11.61/1.99  
% 11.61/1.99  ------ Debug Options
% 11.61/1.99  
% 11.61/1.99  --dbg_backtrace                         false
% 11.61/1.99  --dbg_dump_prop_clauses                 false
% 11.61/1.99  --dbg_dump_prop_clauses_file            -
% 11.61/1.99  --dbg_out_stat                          false
% 11.61/1.99  
% 11.61/1.99  
% 11.61/1.99  
% 11.61/1.99  
% 11.61/1.99  ------ Proving...
% 11.61/1.99  
% 11.61/1.99  
% 11.61/1.99  % SZS status Theorem for theBenchmark.p
% 11.61/1.99  
% 11.61/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.61/1.99  
% 11.61/1.99  fof(f11,conjecture,(
% 11.61/1.99    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1)))),
% 11.61/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.61/1.99  
% 11.61/1.99  fof(f12,negated_conjecture,(
% 11.61/1.99    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1)))),
% 11.61/1.99    inference(negated_conjecture,[],[f11])).
% 11.61/1.99  
% 11.61/1.99  fof(f33,plain,(
% 11.61/1.99    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)))),
% 11.61/1.99    inference(ennf_transformation,[],[f12])).
% 11.61/1.99  
% 11.61/1.99  fof(f34,plain,(
% 11.61/1.99    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 11.61/1.99    inference(flattening,[],[f33])).
% 11.61/1.99  
% 11.61/1.99  fof(f47,plain,(
% 11.61/1.99    ( ! [X0,X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) => (k12_lattice3(X0,X1,k13_lattice3(X0,X1,sK4)) != X1 & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 11.61/1.99    introduced(choice_axiom,[])).
% 11.61/1.99  
% 11.61/1.99  fof(f46,plain,(
% 11.61/1.99    ( ! [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k12_lattice3(X0,sK3,k13_lattice3(X0,sK3,X2)) != sK3 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 11.61/1.99    introduced(choice_axiom,[])).
% 11.61/1.99  
% 11.61/1.99  fof(f45,plain,(
% 11.61/1.99    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => (? [X1] : (? [X2] : (k12_lattice3(sK2,X1,k13_lattice3(sK2,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_orders_2(sK2) & v2_lattice3(sK2) & v1_lattice3(sK2) & v5_orders_2(sK2) & v3_orders_2(sK2))),
% 11.61/1.99    introduced(choice_axiom,[])).
% 11.61/1.99  
% 11.61/1.99  fof(f48,plain,(
% 11.61/1.99    ((k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 & m1_subset_1(sK4,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_orders_2(sK2) & v2_lattice3(sK2) & v1_lattice3(sK2) & v5_orders_2(sK2) & v3_orders_2(sK2)),
% 11.61/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f34,f47,f46,f45])).
% 11.61/1.99  
% 11.61/1.99  fof(f76,plain,(
% 11.61/1.99    m1_subset_1(sK3,u1_struct_0(sK2))),
% 11.61/1.99    inference(cnf_transformation,[],[f48])).
% 11.61/1.99  
% 11.61/1.99  fof(f3,axiom,(
% 11.61/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 11.61/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.61/1.99  
% 11.61/1.99  fof(f17,plain,(
% 11.61/1.99    ! [X0,X1,X2] : (m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 11.61/1.99    inference(ennf_transformation,[],[f3])).
% 11.61/1.99  
% 11.61/1.99  fof(f18,plain,(
% 11.61/1.99    ! [X0,X1,X2] : (m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 11.61/1.99    inference(flattening,[],[f17])).
% 11.61/1.99  
% 11.61/1.99  fof(f51,plain,(
% 11.61/1.99    ( ! [X2,X0,X1] : (m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 11.61/1.99    inference(cnf_transformation,[],[f18])).
% 11.61/1.99  
% 11.61/1.99  fof(f74,plain,(
% 11.61/1.99    v2_lattice3(sK2)),
% 11.61/1.99    inference(cnf_transformation,[],[f48])).
% 11.61/1.99  
% 11.61/1.99  fof(f72,plain,(
% 11.61/1.99    v5_orders_2(sK2)),
% 11.61/1.99    inference(cnf_transformation,[],[f48])).
% 11.61/1.99  
% 11.61/1.99  fof(f75,plain,(
% 11.61/1.99    l1_orders_2(sK2)),
% 11.61/1.99    inference(cnf_transformation,[],[f48])).
% 11.61/1.99  
% 11.61/1.99  fof(f8,axiom,(
% 11.61/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2))),
% 11.61/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.61/1.99  
% 11.61/1.99  fof(f27,plain,(
% 11.61/1.99    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 11.61/1.99    inference(ennf_transformation,[],[f8])).
% 11.61/1.99  
% 11.61/1.99  fof(f28,plain,(
% 11.61/1.99    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 11.61/1.99    inference(flattening,[],[f27])).
% 11.61/1.99  
% 11.61/1.99  fof(f68,plain,(
% 11.61/1.99    ( ! [X2,X0,X1] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 11.61/1.99    inference(cnf_transformation,[],[f28])).
% 11.61/1.99  
% 11.61/1.99  fof(f73,plain,(
% 11.61/1.99    v1_lattice3(sK2)),
% 11.61/1.99    inference(cnf_transformation,[],[f48])).
% 11.61/1.99  
% 11.61/1.99  fof(f10,axiom,(
% 11.61/1.99    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2)))),
% 11.61/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.61/1.99  
% 11.61/1.99  fof(f31,plain,(
% 11.61/1.99    ! [X0] : (! [X1] : (! [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)))),
% 11.61/1.99    inference(ennf_transformation,[],[f10])).
% 11.61/1.99  
% 11.61/1.99  fof(f32,plain,(
% 11.61/1.99    ! [X0] : (! [X1] : (! [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 11.61/1.99    inference(flattening,[],[f31])).
% 11.61/1.99  
% 11.61/1.99  fof(f70,plain,(
% 11.61/1.99    ( ! [X2,X0,X1] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)) )),
% 11.61/1.99    inference(cnf_transformation,[],[f32])).
% 11.61/1.99  
% 11.61/1.99  fof(f71,plain,(
% 11.61/1.99    v3_orders_2(sK2)),
% 11.61/1.99    inference(cnf_transformation,[],[f48])).
% 11.61/1.99  
% 11.61/1.99  fof(f9,axiom,(
% 11.61/1.99    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1))))),
% 11.61/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.61/1.99  
% 11.61/1.99  fof(f29,plain,(
% 11.61/1.99    ! [X0] : (! [X1] : (! [X2] : (k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 11.61/1.99    inference(ennf_transformation,[],[f9])).
% 11.61/1.99  
% 11.61/1.99  fof(f30,plain,(
% 11.61/1.99    ! [X0] : (! [X1] : (! [X2] : (k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 11.61/1.99    inference(flattening,[],[f29])).
% 11.61/1.99  
% 11.61/1.99  fof(f69,plain,(
% 11.61/1.99    ( ! [X2,X0,X1] : (k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 11.61/1.99    inference(cnf_transformation,[],[f30])).
% 11.61/1.99  
% 11.61/1.99  fof(f5,axiom,(
% 11.61/1.99    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 11.61/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.61/1.99  
% 11.61/1.99  fof(f21,plain,(
% 11.61/1.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 11.61/1.99    inference(ennf_transformation,[],[f5])).
% 11.61/1.99  
% 11.61/1.99  fof(f22,plain,(
% 11.61/1.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 11.61/1.99    inference(flattening,[],[f21])).
% 11.61/1.99  
% 11.61/1.99  fof(f35,plain,(
% 11.61/1.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3))) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 11.61/1.99    inference(nnf_transformation,[],[f22])).
% 11.61/1.99  
% 11.61/1.99  fof(f36,plain,(
% 11.61/1.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 11.61/1.99    inference(flattening,[],[f35])).
% 11.61/1.99  
% 11.61/1.99  fof(f37,plain,(
% 11.61/1.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 11.61/1.99    inference(rectify,[],[f36])).
% 11.61/1.99  
% 11.61/1.99  fof(f38,plain,(
% 11.61/1.99    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,X3,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))))),
% 11.61/1.99    introduced(choice_axiom,[])).
% 11.61/1.99  
% 11.61/1.99  fof(f39,plain,(
% 11.61/1.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,X3,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 11.61/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 11.61/1.99  
% 11.61/1.99  fof(f53,plain,(
% 11.61/1.99    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X1,X3) | k10_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 11.61/1.99    inference(cnf_transformation,[],[f39])).
% 11.61/1.99  
% 11.61/1.99  fof(f81,plain,(
% 11.61/1.99    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 11.61/1.99    inference(equality_resolution,[],[f53])).
% 11.61/1.99  
% 11.61/1.99  fof(f1,axiom,(
% 11.61/1.99    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 11.61/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.61/1.99  
% 11.61/1.99  fof(f13,plain,(
% 11.61/1.99    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 11.61/1.99    inference(ennf_transformation,[],[f1])).
% 11.61/1.99  
% 11.61/1.99  fof(f14,plain,(
% 11.61/1.99    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 11.61/1.99    inference(flattening,[],[f13])).
% 11.61/1.99  
% 11.61/1.99  fof(f49,plain,(
% 11.61/1.99    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 11.61/1.99    inference(cnf_transformation,[],[f14])).
% 11.61/1.99  
% 11.61/1.99  fof(f6,axiom,(
% 11.61/1.99    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 11.61/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.61/1.99  
% 11.61/1.99  fof(f23,plain,(
% 11.61/1.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 11.61/1.99    inference(ennf_transformation,[],[f6])).
% 11.61/1.99  
% 11.61/1.99  fof(f24,plain,(
% 11.61/1.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 11.61/1.99    inference(flattening,[],[f23])).
% 11.61/1.99  
% 11.61/1.99  fof(f40,plain,(
% 11.61/1.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 11.61/1.99    inference(nnf_transformation,[],[f24])).
% 11.61/1.99  
% 11.61/1.99  fof(f41,plain,(
% 11.61/1.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 11.61/1.99    inference(flattening,[],[f40])).
% 11.61/1.99  
% 11.61/1.99  fof(f42,plain,(
% 11.61/1.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 11.61/1.99    inference(rectify,[],[f41])).
% 11.61/1.99  
% 11.61/1.99  fof(f43,plain,(
% 11.61/1.99    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK1(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X1) & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0))))),
% 11.61/1.99    introduced(choice_axiom,[])).
% 11.61/1.99  
% 11.61/1.99  fof(f44,plain,(
% 11.61/1.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,sK1(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X1) & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 11.61/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f42,f43])).
% 11.61/1.99  
% 11.61/1.99  fof(f66,plain,(
% 11.61/1.99    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,sK1(X0,X1,X2,X3),X3) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 11.61/1.99    inference(cnf_transformation,[],[f44])).
% 11.61/1.99  
% 11.61/1.99  fof(f2,axiom,(
% 11.61/1.99    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 11.61/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.61/1.99  
% 11.61/1.99  fof(f15,plain,(
% 11.61/1.99    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 11.61/1.99    inference(ennf_transformation,[],[f2])).
% 11.61/1.99  
% 11.61/1.99  fof(f16,plain,(
% 11.61/1.99    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 11.61/1.99    inference(flattening,[],[f15])).
% 11.61/1.99  
% 11.61/1.99  fof(f50,plain,(
% 11.61/1.99    ( ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0)) )),
% 11.61/1.99    inference(cnf_transformation,[],[f16])).
% 11.61/1.99  
% 11.61/1.99  fof(f64,plain,(
% 11.61/1.99    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | r1_orders_2(X0,sK1(X0,X1,X2,X3),X1) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 11.61/1.99    inference(cnf_transformation,[],[f44])).
% 11.61/1.99  
% 11.61/1.99  fof(f77,plain,(
% 11.61/1.99    m1_subset_1(sK4,u1_struct_0(sK2))),
% 11.61/1.99    inference(cnf_transformation,[],[f48])).
% 11.61/1.99  
% 11.61/1.99  fof(f4,axiom,(
% 11.61/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 11.61/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.61/1.99  
% 11.61/1.99  fof(f19,plain,(
% 11.61/1.99    ! [X0,X1,X2] : (m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 11.61/1.99    inference(ennf_transformation,[],[f4])).
% 11.61/1.99  
% 11.61/1.99  fof(f20,plain,(
% 11.61/1.99    ! [X0,X1,X2] : (m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 11.61/1.99    inference(flattening,[],[f19])).
% 11.61/1.99  
% 11.61/1.99  fof(f52,plain,(
% 11.61/1.99    ( ! [X2,X0,X1] : (m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 11.61/1.99    inference(cnf_transformation,[],[f20])).
% 11.61/1.99  
% 11.61/1.99  fof(f7,axiom,(
% 11.61/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2))),
% 11.61/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.61/1.99  
% 11.61/1.99  fof(f25,plain,(
% 11.61/1.99    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 11.61/1.99    inference(ennf_transformation,[],[f7])).
% 11.61/1.99  
% 11.61/1.99  fof(f26,plain,(
% 11.61/1.99    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 11.61/1.99    inference(flattening,[],[f25])).
% 11.61/1.99  
% 11.61/1.99  fof(f67,plain,(
% 11.61/1.99    ( ! [X2,X0,X1] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 11.61/1.99    inference(cnf_transformation,[],[f26])).
% 11.61/1.99  
% 11.61/1.99  fof(f78,plain,(
% 11.61/1.99    k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3),
% 11.61/1.99    inference(cnf_transformation,[],[f48])).
% 11.61/1.99  
% 11.61/1.99  cnf(c_24,negated_conjecture,
% 11.61/1.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 11.61/1.99      inference(cnf_transformation,[],[f76]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_1209,negated_conjecture,
% 11.61/1.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 11.61/1.99      inference(subtyping,[status(esa)],[c_24]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_1592,plain,
% 11.61/1.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 11.61/1.99      inference(predicate_to_equality,[status(thm)],[c_1209]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_2,plain,
% 11.61/1.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.61/1.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.61/1.99      | m1_subset_1(k12_lattice3(X1,X2,X0),u1_struct_0(X1))
% 11.61/1.99      | ~ v5_orders_2(X1)
% 11.61/1.99      | ~ v2_lattice3(X1)
% 11.61/1.99      | ~ l1_orders_2(X1) ),
% 11.61/1.99      inference(cnf_transformation,[],[f51]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_26,negated_conjecture,
% 11.61/1.99      ( v2_lattice3(sK2) ),
% 11.61/1.99      inference(cnf_transformation,[],[f74]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_636,plain,
% 11.61/1.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.61/1.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.61/1.99      | m1_subset_1(k12_lattice3(X1,X2,X0),u1_struct_0(X1))
% 11.61/1.99      | ~ v5_orders_2(X1)
% 11.61/1.99      | ~ l1_orders_2(X1)
% 11.61/1.99      | sK2 != X1 ),
% 11.61/1.99      inference(resolution_lifted,[status(thm)],[c_2,c_26]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_637,plain,
% 11.61/1.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.61/1.99      | m1_subset_1(k12_lattice3(sK2,X0,X1),u1_struct_0(sK2))
% 11.61/1.99      | ~ v5_orders_2(sK2)
% 11.61/1.99      | ~ l1_orders_2(sK2) ),
% 11.61/1.99      inference(unflattening,[status(thm)],[c_636]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_28,negated_conjecture,
% 11.61/1.99      ( v5_orders_2(sK2) ),
% 11.61/1.99      inference(cnf_transformation,[],[f72]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_25,negated_conjecture,
% 11.61/1.99      ( l1_orders_2(sK2) ),
% 11.61/1.99      inference(cnf_transformation,[],[f75]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_641,plain,
% 11.61/1.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.61/1.99      | m1_subset_1(k12_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
% 11.61/1.99      inference(global_propositional_subsumption,
% 11.61/1.99                [status(thm)],
% 11.61/1.99                [c_637,c_28,c_25]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_1199,plain,
% 11.61/1.99      ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 11.61/1.99      | m1_subset_1(k12_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) ),
% 11.61/1.99      inference(subtyping,[status(esa)],[c_641]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_1602,plain,
% 11.61/1.99      ( m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 11.61/1.99      | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top
% 11.61/1.99      | m1_subset_1(k12_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) = iProver_top ),
% 11.61/1.99      inference(predicate_to_equality,[status(thm)],[c_1199]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_19,plain,
% 11.61/1.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.61/1.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.61/1.99      | ~ v5_orders_2(X1)
% 11.61/1.99      | ~ l1_orders_2(X1)
% 11.61/1.99      | ~ v1_lattice3(X1)
% 11.61/1.99      | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0) ),
% 11.61/1.99      inference(cnf_transformation,[],[f68]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_27,negated_conjecture,
% 11.61/1.99      ( v1_lattice3(sK2) ),
% 11.61/1.99      inference(cnf_transformation,[],[f73]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_941,plain,
% 11.61/1.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.61/1.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.61/1.99      | ~ v5_orders_2(X1)
% 11.61/1.99      | ~ l1_orders_2(X1)
% 11.61/1.99      | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0)
% 11.61/1.99      | sK2 != X1 ),
% 11.61/1.99      inference(resolution_lifted,[status(thm)],[c_19,c_27]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_942,plain,
% 11.61/1.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.61/1.99      | ~ v5_orders_2(sK2)
% 11.61/1.99      | ~ l1_orders_2(sK2)
% 11.61/1.99      | k10_lattice3(sK2,X0,X1) = k13_lattice3(sK2,X0,X1) ),
% 11.61/1.99      inference(unflattening,[status(thm)],[c_941]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_946,plain,
% 11.61/1.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.61/1.99      | k10_lattice3(sK2,X0,X1) = k13_lattice3(sK2,X0,X1) ),
% 11.61/1.99      inference(global_propositional_subsumption,
% 11.61/1.99                [status(thm)],
% 11.61/1.99                [c_942,c_28,c_25]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_1190,plain,
% 11.61/1.99      ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 11.61/1.99      | k10_lattice3(sK2,X0_46,X1_46) = k13_lattice3(sK2,X0_46,X1_46) ),
% 11.61/1.99      inference(subtyping,[status(esa)],[c_946]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_1611,plain,
% 11.61/1.99      ( k10_lattice3(sK2,X0_46,X1_46) = k13_lattice3(sK2,X0_46,X1_46)
% 11.61/1.99      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 11.61/1.99      | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top ),
% 11.61/1.99      inference(predicate_to_equality,[status(thm)],[c_1190]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_5215,plain,
% 11.61/1.99      ( k10_lattice3(sK2,k12_lattice3(sK2,X0_46,X1_46),X2_46) = k13_lattice3(sK2,k12_lattice3(sK2,X0_46,X1_46),X2_46)
% 11.61/1.99      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 11.61/1.99      | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top
% 11.61/1.99      | m1_subset_1(X2_46,u1_struct_0(sK2)) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_1602,c_1611]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_29828,plain,
% 11.61/1.99      ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,X0_46),X1_46) = k13_lattice3(sK2,k12_lattice3(sK2,sK3,X0_46),X1_46)
% 11.61/1.99      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 11.61/1.99      | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_1592,c_5215]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_30708,plain,
% 11.61/1.99      ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK3),X0_46) = k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK3),X0_46)
% 11.61/1.99      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_1592,c_29828]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_31395,plain,
% 11.61/1.99      ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK3),sK3) = k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK3),sK3) ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_1592,c_30708]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_21,plain,
% 11.61/1.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.61/1.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.61/1.99      | ~ v3_orders_2(X1)
% 11.61/1.99      | ~ v5_orders_2(X1)
% 11.61/1.99      | ~ v2_lattice3(X1)
% 11.61/1.99      | ~ l1_orders_2(X1)
% 11.61/1.99      | ~ v1_lattice3(X1)
% 11.61/1.99      | k13_lattice3(X1,k12_lattice3(X1,X2,X0),X0) = X0 ),
% 11.61/1.99      inference(cnf_transformation,[],[f70]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_29,negated_conjecture,
% 11.61/1.99      ( v3_orders_2(sK2) ),
% 11.61/1.99      inference(cnf_transformation,[],[f71]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_385,plain,
% 11.61/1.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.61/1.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.61/1.99      | ~ v5_orders_2(X1)
% 11.61/1.99      | ~ v2_lattice3(X1)
% 11.61/1.99      | ~ l1_orders_2(X1)
% 11.61/1.99      | ~ v1_lattice3(X1)
% 11.61/1.99      | k13_lattice3(X1,k12_lattice3(X1,X2,X0),X0) = X0
% 11.61/1.99      | sK2 != X1 ),
% 11.61/1.99      inference(resolution_lifted,[status(thm)],[c_21,c_29]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_386,plain,
% 11.61/1.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.61/1.99      | ~ v5_orders_2(sK2)
% 11.61/1.99      | ~ v2_lattice3(sK2)
% 11.61/1.99      | ~ l1_orders_2(sK2)
% 11.61/1.99      | ~ v1_lattice3(sK2)
% 11.61/1.99      | k13_lattice3(sK2,k12_lattice3(sK2,X0,X1),X1) = X1 ),
% 11.61/1.99      inference(unflattening,[status(thm)],[c_385]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_390,plain,
% 11.61/1.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.61/1.99      | k13_lattice3(sK2,k12_lattice3(sK2,X0,X1),X1) = X1 ),
% 11.61/1.99      inference(global_propositional_subsumption,
% 11.61/1.99                [status(thm)],
% 11.61/1.99                [c_386,c_28,c_27,c_26,c_25]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_1208,plain,
% 11.61/1.99      ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 11.61/1.99      | k13_lattice3(sK2,k12_lattice3(sK2,X0_46,X1_46),X1_46) = X1_46 ),
% 11.61/1.99      inference(subtyping,[status(esa)],[c_390]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_1593,plain,
% 11.61/1.99      ( k13_lattice3(sK2,k12_lattice3(sK2,X0_46,X1_46),X1_46) = X1_46
% 11.61/1.99      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 11.61/1.99      | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top ),
% 11.61/1.99      inference(predicate_to_equality,[status(thm)],[c_1208]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_1883,plain,
% 11.61/1.99      ( k13_lattice3(sK2,k12_lattice3(sK2,sK3,X0_46),X0_46) = X0_46
% 11.61/1.99      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_1592,c_1593]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_1991,plain,
% 11.61/1.99      ( k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK3),sK3) = sK3 ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_1592,c_1883]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_5214,plain,
% 11.61/1.99      ( k10_lattice3(sK2,sK3,X0_46) = k13_lattice3(sK2,sK3,X0_46)
% 11.61/1.99      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_1592,c_1611]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_5872,plain,
% 11.61/1.99      ( k10_lattice3(sK2,sK3,k12_lattice3(sK2,X0_46,X1_46)) = k13_lattice3(sK2,sK3,k12_lattice3(sK2,X0_46,X1_46))
% 11.61/1.99      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 11.61/1.99      | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_1602,c_5214]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_21114,plain,
% 11.61/1.99      ( k10_lattice3(sK2,sK3,k12_lattice3(sK2,sK3,X0_46)) = k13_lattice3(sK2,sK3,k12_lattice3(sK2,sK3,X0_46))
% 11.61/1.99      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_1592,c_5872]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_22115,plain,
% 11.61/1.99      ( k10_lattice3(sK2,sK3,k12_lattice3(sK2,sK3,sK3)) = k13_lattice3(sK2,sK3,k12_lattice3(sK2,sK3,sK3)) ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_1592,c_21114]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_20,plain,
% 11.61/1.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.61/1.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.61/1.99      | ~ v5_orders_2(X1)
% 11.61/1.99      | ~ l1_orders_2(X1)
% 11.61/1.99      | ~ v1_lattice3(X1)
% 11.61/1.99      | k10_lattice3(X1,X0,X2) = k10_lattice3(X1,X2,X0) ),
% 11.61/1.99      inference(cnf_transformation,[],[f69]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_920,plain,
% 11.61/1.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.61/1.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.61/1.99      | ~ v5_orders_2(X1)
% 11.61/1.99      | ~ l1_orders_2(X1)
% 11.61/1.99      | k10_lattice3(X1,X0,X2) = k10_lattice3(X1,X2,X0)
% 11.61/1.99      | sK2 != X1 ),
% 11.61/1.99      inference(resolution_lifted,[status(thm)],[c_20,c_27]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_921,plain,
% 11.61/1.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.61/1.99      | ~ v5_orders_2(sK2)
% 11.61/1.99      | ~ l1_orders_2(sK2)
% 11.61/1.99      | k10_lattice3(sK2,X1,X0) = k10_lattice3(sK2,X0,X1) ),
% 11.61/1.99      inference(unflattening,[status(thm)],[c_920]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_925,plain,
% 11.61/1.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.61/1.99      | k10_lattice3(sK2,X1,X0) = k10_lattice3(sK2,X0,X1) ),
% 11.61/1.99      inference(global_propositional_subsumption,
% 11.61/1.99                [status(thm)],
% 11.61/1.99                [c_921,c_28,c_25]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_1191,plain,
% 11.61/1.99      ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 11.61/1.99      | k10_lattice3(sK2,X1_46,X0_46) = k10_lattice3(sK2,X0_46,X1_46) ),
% 11.61/1.99      inference(subtyping,[status(esa)],[c_925]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_1610,plain,
% 11.61/1.99      ( k10_lattice3(sK2,X0_46,X1_46) = k10_lattice3(sK2,X1_46,X0_46)
% 11.61/1.99      | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top
% 11.61/1.99      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top ),
% 11.61/1.99      inference(predicate_to_equality,[status(thm)],[c_1191]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_3810,plain,
% 11.61/1.99      ( k10_lattice3(sK2,X0_46,sK3) = k10_lattice3(sK2,sK3,X0_46)
% 11.61/1.99      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_1592,c_1610]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_4082,plain,
% 11.61/1.99      ( k10_lattice3(sK2,sK3,k12_lattice3(sK2,X0_46,X1_46)) = k10_lattice3(sK2,k12_lattice3(sK2,X0_46,X1_46),sK3)
% 11.61/1.99      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 11.61/1.99      | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_1602,c_3810]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_16904,plain,
% 11.61/1.99      ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,X0_46),sK3) = k10_lattice3(sK2,sK3,k12_lattice3(sK2,sK3,X0_46))
% 11.61/1.99      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_1592,c_4082]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_17708,plain,
% 11.61/1.99      ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK3),sK3) = k10_lattice3(sK2,sK3,k12_lattice3(sK2,sK3,sK3)) ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_1592,c_16904]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_23381,plain,
% 11.61/1.99      ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK3),sK3) = k13_lattice3(sK2,sK3,k12_lattice3(sK2,sK3,sK3)) ),
% 11.61/1.99      inference(demodulation,[status(thm)],[c_22115,c_17708]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_31441,plain,
% 11.61/1.99      ( k13_lattice3(sK2,sK3,k12_lattice3(sK2,sK3,sK3)) = sK3 ),
% 11.61/1.99      inference(light_normalisation,
% 11.61/1.99                [status(thm)],
% 11.61/1.99                [c_31395,c_1991,c_23381]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_32108,plain,
% 11.61/1.99      ( k10_lattice3(sK2,sK3,k12_lattice3(sK2,sK3,sK3)) = sK3 ),
% 11.61/1.99      inference(demodulation,[status(thm)],[c_31441,c_22115]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_10,plain,
% 11.61/1.99      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 11.61/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.61/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.61/1.99      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 11.61/1.99      | ~ v5_orders_2(X0)
% 11.61/1.99      | ~ l1_orders_2(X0)
% 11.61/1.99      | ~ v1_lattice3(X0)
% 11.61/1.99      | v2_struct_0(X0) ),
% 11.61/1.99      inference(cnf_transformation,[],[f81]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_0,plain,
% 11.61/1.99      ( ~ l1_orders_2(X0) | ~ v1_lattice3(X0) | ~ v2_struct_0(X0) ),
% 11.61/1.99      inference(cnf_transformation,[],[f49]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_210,plain,
% 11.61/1.99      ( ~ v1_lattice3(X0)
% 11.61/1.99      | ~ l1_orders_2(X0)
% 11.61/1.99      | ~ v5_orders_2(X0)
% 11.61/1.99      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 11.61/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.61/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.61/1.99      | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) ),
% 11.61/1.99      inference(global_propositional_subsumption,
% 11.61/1.99                [status(thm)],
% 11.61/1.99                [c_10,c_0]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_211,plain,
% 11.61/1.99      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 11.61/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.61/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.61/1.99      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 11.61/1.99      | ~ v5_orders_2(X0)
% 11.61/1.99      | ~ l1_orders_2(X0)
% 11.61/1.99      | ~ v1_lattice3(X0) ),
% 11.61/1.99      inference(renaming,[status(thm)],[c_210]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_900,plain,
% 11.61/1.99      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 11.61/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.61/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.61/1.99      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 11.61/1.99      | ~ v5_orders_2(X0)
% 11.61/1.99      | ~ l1_orders_2(X0)
% 11.61/1.99      | sK2 != X0 ),
% 11.61/1.99      inference(resolution_lifted,[status(thm)],[c_211,c_27]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_901,plain,
% 11.61/1.99      ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
% 11.61/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2))
% 11.61/1.99      | ~ v5_orders_2(sK2)
% 11.61/1.99      | ~ l1_orders_2(sK2) ),
% 11.61/1.99      inference(unflattening,[status(thm)],[c_900]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_903,plain,
% 11.61/1.99      ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
% 11.61/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
% 11.61/1.99      inference(global_propositional_subsumption,
% 11.61/1.99                [status(thm)],
% 11.61/1.99                [c_901,c_28,c_25]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_904,plain,
% 11.61/1.99      ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
% 11.61/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
% 11.61/1.99      inference(renaming,[status(thm)],[c_903]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_1192,plain,
% 11.61/1.99      ( r1_orders_2(sK2,X0_46,k10_lattice3(sK2,X0_46,X1_46))
% 11.61/1.99      | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(k10_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) ),
% 11.61/1.99      inference(subtyping,[status(esa)],[c_904]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_1609,plain,
% 11.61/1.99      ( r1_orders_2(sK2,X0_46,k10_lattice3(sK2,X0_46,X1_46)) = iProver_top
% 11.61/1.99      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 11.61/1.99      | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top
% 11.61/1.99      | m1_subset_1(k10_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) != iProver_top ),
% 11.61/1.99      inference(predicate_to_equality,[status(thm)],[c_1192]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_33424,plain,
% 11.61/1.99      ( r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,k12_lattice3(sK2,sK3,sK3))) = iProver_top
% 11.61/1.99      | m1_subset_1(k12_lattice3(sK2,sK3,sK3),u1_struct_0(sK2)) != iProver_top
% 11.61/1.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_32108,c_1609]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_33441,plain,
% 11.61/1.99      ( r1_orders_2(sK2,sK3,sK3) = iProver_top
% 11.61/1.99      | m1_subset_1(k12_lattice3(sK2,sK3,sK3),u1_struct_0(sK2)) != iProver_top
% 11.61/1.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 11.61/1.99      inference(light_normalisation,[status(thm)],[c_33424,c_32108]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_11,plain,
% 11.61/1.99      ( ~ r1_orders_2(X0,X1,X2)
% 11.61/1.99      | ~ r1_orders_2(X0,X1,X3)
% 11.61/1.99      | ~ r1_orders_2(X0,sK1(X0,X3,X2,X1),X1)
% 11.61/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.61/1.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 11.61/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.61/1.99      | ~ v5_orders_2(X0)
% 11.61/1.99      | ~ v2_lattice3(X0)
% 11.61/1.99      | ~ l1_orders_2(X0)
% 11.61/1.99      | v2_struct_0(X0)
% 11.61/1.99      | k11_lattice3(X0,X3,X2) = X1 ),
% 11.61/1.99      inference(cnf_transformation,[],[f66]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_1,plain,
% 11.61/1.99      ( ~ v2_lattice3(X0) | ~ l1_orders_2(X0) | ~ v2_struct_0(X0) ),
% 11.61/1.99      inference(cnf_transformation,[],[f50]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_203,plain,
% 11.61/1.99      ( ~ l1_orders_2(X0)
% 11.61/1.99      | ~ v2_lattice3(X0)
% 11.61/1.99      | ~ v5_orders_2(X0)
% 11.61/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.61/1.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 11.61/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.61/1.99      | ~ r1_orders_2(X0,sK1(X0,X3,X2,X1),X1)
% 11.61/1.99      | ~ r1_orders_2(X0,X1,X3)
% 11.61/1.99      | ~ r1_orders_2(X0,X1,X2)
% 11.61/1.99      | k11_lattice3(X0,X3,X2) = X1 ),
% 11.61/1.99      inference(global_propositional_subsumption,
% 11.61/1.99                [status(thm)],
% 11.61/1.99                [c_11,c_1]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_204,plain,
% 11.61/1.99      ( ~ r1_orders_2(X0,X1,X2)
% 11.61/1.99      | ~ r1_orders_2(X0,X1,X3)
% 11.61/1.99      | ~ r1_orders_2(X0,sK1(X0,X2,X3,X1),X1)
% 11.61/1.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 11.61/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.61/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.61/1.99      | ~ v5_orders_2(X0)
% 11.61/1.99      | ~ v2_lattice3(X0)
% 11.61/1.99      | ~ l1_orders_2(X0)
% 11.61/1.99      | k11_lattice3(X0,X2,X3) = X1 ),
% 11.61/1.99      inference(renaming,[status(thm)],[c_203]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_410,plain,
% 11.61/1.99      ( ~ r1_orders_2(X0,X1,X2)
% 11.61/1.99      | ~ r1_orders_2(X0,X1,X3)
% 11.61/1.99      | ~ r1_orders_2(X0,sK1(X0,X3,X2,X1),X1)
% 11.61/1.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 11.61/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.61/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.61/1.99      | ~ v5_orders_2(X0)
% 11.61/1.99      | ~ l1_orders_2(X0)
% 11.61/1.99      | k11_lattice3(X0,X3,X2) = X1
% 11.61/1.99      | sK2 != X0 ),
% 11.61/1.99      inference(resolution_lifted,[status(thm)],[c_204,c_26]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_411,plain,
% 11.61/1.99      ( ~ r1_orders_2(sK2,X0,X1)
% 11.61/1.99      | ~ r1_orders_2(sK2,X0,X2)
% 11.61/1.99      | ~ r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X0)
% 11.61/1.99      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.61/1.99      | ~ v5_orders_2(sK2)
% 11.61/1.99      | ~ l1_orders_2(sK2)
% 11.61/1.99      | k11_lattice3(sK2,X1,X2) = X0 ),
% 11.61/1.99      inference(unflattening,[status(thm)],[c_410]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_415,plain,
% 11.61/1.99      ( ~ r1_orders_2(sK2,X0,X1)
% 11.61/1.99      | ~ r1_orders_2(sK2,X0,X2)
% 11.61/1.99      | ~ r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X0)
% 11.61/1.99      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.61/1.99      | k11_lattice3(sK2,X1,X2) = X0 ),
% 11.61/1.99      inference(global_propositional_subsumption,
% 11.61/1.99                [status(thm)],
% 11.61/1.99                [c_411,c_28,c_25]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_1207,plain,
% 11.61/1.99      ( ~ r1_orders_2(sK2,X0_46,X1_46)
% 11.61/1.99      | ~ r1_orders_2(sK2,X0_46,X2_46)
% 11.61/1.99      | ~ r1_orders_2(sK2,sK1(sK2,X1_46,X2_46,X0_46),X0_46)
% 11.61/1.99      | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(X2_46,u1_struct_0(sK2))
% 11.61/1.99      | k11_lattice3(sK2,X1_46,X2_46) = X0_46 ),
% 11.61/1.99      inference(subtyping,[status(esa)],[c_415]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_32589,plain,
% 11.61/1.99      ( ~ r1_orders_2(sK2,X0_46,k13_lattice3(sK2,sK3,sK4))
% 11.61/1.99      | ~ r1_orders_2(sK2,X0_46,sK3)
% 11.61/1.99      | ~ r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_46),X0_46)
% 11.61/1.99      | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 11.61/1.99      | k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46 ),
% 11.61/1.99      inference(instantiation,[status(thm)],[c_1207]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_32605,plain,
% 11.61/1.99      ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46
% 11.61/1.99      | r1_orders_2(sK2,X0_46,k13_lattice3(sK2,sK3,sK4)) != iProver_top
% 11.61/1.99      | r1_orders_2(sK2,X0_46,sK3) != iProver_top
% 11.61/1.99      | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_46),X0_46) != iProver_top
% 11.61/1.99      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 11.61/1.99      | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 11.61/1.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 11.61/1.99      inference(predicate_to_equality,[status(thm)],[c_32589]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_32607,plain,
% 11.61/1.99      ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
% 11.61/1.99      | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),sK3),sK3) != iProver_top
% 11.61/1.99      | r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != iProver_top
% 11.61/1.99      | r1_orders_2(sK2,sK3,sK3) != iProver_top
% 11.61/1.99      | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 11.61/1.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 11.61/1.99      inference(instantiation,[status(thm)],[c_32605]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_13,plain,
% 11.61/1.99      ( ~ r1_orders_2(X0,X1,X2)
% 11.61/1.99      | ~ r1_orders_2(X0,X1,X3)
% 11.61/1.99      | r1_orders_2(X0,sK1(X0,X3,X2,X1),X3)
% 11.61/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.61/1.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 11.61/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.61/1.99      | ~ v5_orders_2(X0)
% 11.61/1.99      | ~ v2_lattice3(X0)
% 11.61/1.99      | ~ l1_orders_2(X0)
% 11.61/1.99      | v2_struct_0(X0)
% 11.61/1.99      | k11_lattice3(X0,X3,X2) = X1 ),
% 11.61/1.99      inference(cnf_transformation,[],[f64]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_191,plain,
% 11.61/1.99      ( ~ l1_orders_2(X0)
% 11.61/1.99      | ~ v2_lattice3(X0)
% 11.61/1.99      | ~ v5_orders_2(X0)
% 11.61/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.61/1.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 11.61/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.61/1.99      | r1_orders_2(X0,sK1(X0,X3,X2,X1),X3)
% 11.61/1.99      | ~ r1_orders_2(X0,X1,X3)
% 11.61/1.99      | ~ r1_orders_2(X0,X1,X2)
% 11.61/1.99      | k11_lattice3(X0,X3,X2) = X1 ),
% 11.61/1.99      inference(global_propositional_subsumption,
% 11.61/1.99                [status(thm)],
% 11.61/1.99                [c_13,c_1]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_192,plain,
% 11.61/1.99      ( ~ r1_orders_2(X0,X1,X2)
% 11.61/1.99      | ~ r1_orders_2(X0,X1,X3)
% 11.61/1.99      | r1_orders_2(X0,sK1(X0,X2,X3,X1),X2)
% 11.61/1.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 11.61/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.61/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.61/1.99      | ~ v5_orders_2(X0)
% 11.61/1.99      | ~ v2_lattice3(X0)
% 11.61/1.99      | ~ l1_orders_2(X0)
% 11.61/1.99      | k11_lattice3(X0,X2,X3) = X1 ),
% 11.61/1.99      inference(renaming,[status(thm)],[c_191]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_476,plain,
% 11.61/1.99      ( ~ r1_orders_2(X0,X1,X2)
% 11.61/1.99      | ~ r1_orders_2(X0,X1,X3)
% 11.61/1.99      | r1_orders_2(X0,sK1(X0,X3,X2,X1),X3)
% 11.61/1.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 11.61/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.61/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.61/1.99      | ~ v5_orders_2(X0)
% 11.61/1.99      | ~ l1_orders_2(X0)
% 11.61/1.99      | k11_lattice3(X0,X3,X2) = X1
% 11.61/1.99      | sK2 != X0 ),
% 11.61/1.99      inference(resolution_lifted,[status(thm)],[c_192,c_26]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_477,plain,
% 11.61/1.99      ( ~ r1_orders_2(sK2,X0,X1)
% 11.61/1.99      | ~ r1_orders_2(sK2,X0,X2)
% 11.61/1.99      | r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X1)
% 11.61/1.99      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.61/1.99      | ~ v5_orders_2(sK2)
% 11.61/1.99      | ~ l1_orders_2(sK2)
% 11.61/1.99      | k11_lattice3(sK2,X1,X2) = X0 ),
% 11.61/1.99      inference(unflattening,[status(thm)],[c_476]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_479,plain,
% 11.61/1.99      ( ~ r1_orders_2(sK2,X0,X1)
% 11.61/1.99      | ~ r1_orders_2(sK2,X0,X2)
% 11.61/1.99      | r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X1)
% 11.61/1.99      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.61/1.99      | k11_lattice3(sK2,X1,X2) = X0 ),
% 11.61/1.99      inference(global_propositional_subsumption,
% 11.61/1.99                [status(thm)],
% 11.61/1.99                [c_477,c_28,c_25]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_1205,plain,
% 11.61/1.99      ( ~ r1_orders_2(sK2,X0_46,X1_46)
% 11.61/1.99      | ~ r1_orders_2(sK2,X0_46,X2_46)
% 11.61/1.99      | r1_orders_2(sK2,sK1(sK2,X1_46,X2_46,X0_46),X1_46)
% 11.61/1.99      | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(X2_46,u1_struct_0(sK2))
% 11.61/1.99      | k11_lattice3(sK2,X1_46,X2_46) = X0_46 ),
% 11.61/1.99      inference(subtyping,[status(esa)],[c_479]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_32591,plain,
% 11.61/1.99      ( ~ r1_orders_2(sK2,X0_46,k13_lattice3(sK2,sK3,sK4))
% 11.61/1.99      | ~ r1_orders_2(sK2,X0_46,sK3)
% 11.61/1.99      | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_46),sK3)
% 11.61/1.99      | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 11.61/1.99      | k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46 ),
% 11.61/1.99      inference(instantiation,[status(thm)],[c_1205]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_32597,plain,
% 11.61/1.99      ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46
% 11.61/1.99      | r1_orders_2(sK2,X0_46,k13_lattice3(sK2,sK3,sK4)) != iProver_top
% 11.61/1.99      | r1_orders_2(sK2,X0_46,sK3) != iProver_top
% 11.61/1.99      | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),X0_46),sK3) = iProver_top
% 11.61/1.99      | m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 11.61/1.99      | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 11.61/1.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 11.61/1.99      inference(predicate_to_equality,[status(thm)],[c_32591]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_32599,plain,
% 11.61/1.99      ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
% 11.61/1.99      | r1_orders_2(sK2,sK1(sK2,sK3,k13_lattice3(sK2,sK3,sK4),sK3),sK3) = iProver_top
% 11.61/1.99      | r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != iProver_top
% 11.61/1.99      | r1_orders_2(sK2,sK3,sK3) != iProver_top
% 11.61/1.99      | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 11.61/1.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 11.61/1.99      inference(instantiation,[status(thm)],[c_32597]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_1214,plain,
% 11.61/1.99      ( X0_46 != X1_46 | X2_46 != X1_46 | X2_46 = X0_46 ),
% 11.61/1.99      theory(equality) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_2479,plain,
% 11.61/1.99      ( X0_46 != X1_46
% 11.61/1.99      | X0_46 = k11_lattice3(sK2,X2_46,X3_46)
% 11.61/1.99      | k11_lattice3(sK2,X2_46,X3_46) != X1_46 ),
% 11.61/1.99      inference(instantiation,[status(thm)],[c_1214]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_11339,plain,
% 11.61/1.99      ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != X0_46
% 11.61/1.99      | sK3 != X0_46
% 11.61/1.99      | sK3 = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
% 11.61/1.99      inference(instantiation,[status(thm)],[c_2479]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_11340,plain,
% 11.61/1.99      ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3
% 11.61/1.99      | sK3 = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
% 11.61/1.99      | sK3 != sK3 ),
% 11.61/1.99      inference(instantiation,[status(thm)],[c_11339]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_23,negated_conjecture,
% 11.61/1.99      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 11.61/1.99      inference(cnf_transformation,[],[f77]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_1210,negated_conjecture,
% 11.61/1.99      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 11.61/1.99      inference(subtyping,[status(esa)],[c_23]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_1591,plain,
% 11.61/1.99      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 11.61/1.99      inference(predicate_to_equality,[status(thm)],[c_1210]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_5870,plain,
% 11.61/1.99      ( k10_lattice3(sK2,sK3,sK4) = k13_lattice3(sK2,sK3,sK4) ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_1591,c_5214]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_7162,plain,
% 11.61/1.99      ( r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK4)) = iProver_top
% 11.61/1.99      | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 11.61/1.99      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 11.61/1.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_5870,c_1609]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_7178,plain,
% 11.61/1.99      ( r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = iProver_top
% 11.61/1.99      | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 11.61/1.99      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 11.61/1.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 11.61/1.99      inference(light_normalisation,[status(thm)],[c_7162,c_5870]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_1896,plain,
% 11.61/1.99      ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != X0_46
% 11.61/1.99      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
% 11.61/1.99      | sK3 != X0_46 ),
% 11.61/1.99      inference(instantiation,[status(thm)],[c_1214]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_7024,plain,
% 11.61/1.99      ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
% 11.61/1.99      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
% 11.61/1.99      | sK3 != k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
% 11.61/1.99      inference(instantiation,[status(thm)],[c_1896]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_3,plain,
% 11.61/1.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.61/1.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.61/1.99      | m1_subset_1(k13_lattice3(X1,X2,X0),u1_struct_0(X1))
% 11.61/1.99      | ~ v5_orders_2(X1)
% 11.61/1.99      | ~ l1_orders_2(X1)
% 11.61/1.99      | ~ v1_lattice3(X1) ),
% 11.61/1.99      inference(cnf_transformation,[],[f52]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_962,plain,
% 11.61/1.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.61/1.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.61/1.99      | m1_subset_1(k13_lattice3(X1,X2,X0),u1_struct_0(X1))
% 11.61/1.99      | ~ v5_orders_2(X1)
% 11.61/1.99      | ~ l1_orders_2(X1)
% 11.61/1.99      | sK2 != X1 ),
% 11.61/1.99      inference(resolution_lifted,[status(thm)],[c_3,c_27]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_963,plain,
% 11.61/1.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.61/1.99      | m1_subset_1(k13_lattice3(sK2,X0,X1),u1_struct_0(sK2))
% 11.61/1.99      | ~ v5_orders_2(sK2)
% 11.61/1.99      | ~ l1_orders_2(sK2) ),
% 11.61/1.99      inference(unflattening,[status(thm)],[c_962]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_967,plain,
% 11.61/1.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.61/1.99      | m1_subset_1(k13_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
% 11.61/1.99      inference(global_propositional_subsumption,
% 11.61/1.99                [status(thm)],
% 11.61/1.99                [c_963,c_28,c_25]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_1189,plain,
% 11.61/1.99      ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 11.61/1.99      | m1_subset_1(k13_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) ),
% 11.61/1.99      inference(subtyping,[status(esa)],[c_967]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_5027,plain,
% 11.61/1.99      ( m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 11.61/1.99      inference(instantiation,[status(thm)],[c_1189]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_5028,plain,
% 11.61/1.99      ( m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) = iProver_top
% 11.61/1.99      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 11.61/1.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 11.61/1.99      inference(predicate_to_equality,[status(thm)],[c_5027]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_18,plain,
% 11.61/1.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.61/1.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.61/1.99      | ~ v5_orders_2(X1)
% 11.61/1.99      | ~ v2_lattice3(X1)
% 11.61/1.99      | ~ l1_orders_2(X1)
% 11.61/1.99      | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0) ),
% 11.61/1.99      inference(cnf_transformation,[],[f67]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_615,plain,
% 11.61/1.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.61/1.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.61/1.99      | ~ v5_orders_2(X1)
% 11.61/1.99      | ~ l1_orders_2(X1)
% 11.61/1.99      | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0)
% 11.61/1.99      | sK2 != X1 ),
% 11.61/1.99      inference(resolution_lifted,[status(thm)],[c_18,c_26]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_616,plain,
% 11.61/1.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.61/1.99      | ~ v5_orders_2(sK2)
% 11.61/1.99      | ~ l1_orders_2(sK2)
% 11.61/1.99      | k11_lattice3(sK2,X0,X1) = k12_lattice3(sK2,X0,X1) ),
% 11.61/1.99      inference(unflattening,[status(thm)],[c_615]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_620,plain,
% 11.61/1.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 11.61/1.99      | k11_lattice3(sK2,X0,X1) = k12_lattice3(sK2,X0,X1) ),
% 11.61/1.99      inference(global_propositional_subsumption,
% 11.61/1.99                [status(thm)],
% 11.61/1.99                [c_616,c_28,c_25]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_1200,plain,
% 11.61/1.99      ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 11.61/1.99      | k11_lattice3(sK2,X0_46,X1_46) = k12_lattice3(sK2,X0_46,X1_46) ),
% 11.61/1.99      inference(subtyping,[status(esa)],[c_620]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_4468,plain,
% 11.61/1.99      ( ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 11.61/1.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 11.61/1.99      | k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
% 11.61/1.99      inference(instantiation,[status(thm)],[c_1200]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_1921,plain,
% 11.61/1.99      ( X0_46 != X1_46
% 11.61/1.99      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != X1_46
% 11.61/1.99      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46 ),
% 11.61/1.99      inference(instantiation,[status(thm)],[c_1214]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_1983,plain,
% 11.61/1.99      ( X0_46 != k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
% 11.61/1.99      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_46
% 11.61/1.99      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
% 11.61/1.99      inference(instantiation,[status(thm)],[c_1921]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_4467,plain,
% 11.61/1.99      ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
% 11.61/1.99      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
% 11.61/1.99      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
% 11.61/1.99      inference(instantiation,[status(thm)],[c_1983]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_1213,plain,( X0_46 = X0_46 ),theory(equality) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_1920,plain,
% 11.61/1.99      ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
% 11.61/1.99      inference(instantiation,[status(thm)],[c_1213]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_1250,plain,
% 11.61/1.99      ( m1_subset_1(X0_46,u1_struct_0(sK2)) != iProver_top
% 11.61/1.99      | m1_subset_1(X1_46,u1_struct_0(sK2)) != iProver_top
% 11.61/1.99      | m1_subset_1(k12_lattice3(sK2,X0_46,X1_46),u1_struct_0(sK2)) = iProver_top ),
% 11.61/1.99      inference(predicate_to_equality,[status(thm)],[c_1199]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_1252,plain,
% 11.61/1.99      ( m1_subset_1(k12_lattice3(sK2,sK3,sK3),u1_struct_0(sK2)) = iProver_top
% 11.61/1.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 11.61/1.99      inference(instantiation,[status(thm)],[c_1250]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_22,negated_conjecture,
% 11.61/1.99      ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
% 11.61/1.99      inference(cnf_transformation,[],[f78]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_1211,negated_conjecture,
% 11.61/1.99      ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
% 11.61/1.99      inference(subtyping,[status(esa)],[c_22]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_1224,plain,
% 11.61/1.99      ( sK3 = sK3 ),
% 11.61/1.99      inference(instantiation,[status(thm)],[c_1213]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_36,plain,
% 11.61/1.99      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 11.61/1.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_35,plain,
% 11.61/1.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 11.61/1.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(contradiction,plain,
% 11.61/1.99      ( $false ),
% 11.61/1.99      inference(minisat,
% 11.61/1.99                [status(thm)],
% 11.61/1.99                [c_33441,c_32607,c_32599,c_11340,c_7178,c_7024,c_5028,
% 11.61/1.99                 c_5027,c_4468,c_4467,c_1920,c_1252,c_1211,c_1224,c_36,
% 11.61/1.99                 c_23,c_35,c_24]) ).
% 11.61/1.99  
% 11.61/1.99  
% 11.61/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.61/1.99  
% 11.61/1.99  ------                               Statistics
% 11.61/1.99  
% 11.61/1.99  ------ General
% 11.61/1.99  
% 11.61/1.99  abstr_ref_over_cycles:                  0
% 11.61/1.99  abstr_ref_under_cycles:                 0
% 11.61/1.99  gc_basic_clause_elim:                   0
% 11.61/1.99  forced_gc_time:                         0
% 11.61/1.99  parsing_time:                           0.012
% 11.61/1.99  unif_index_cands_time:                  0.
% 11.61/1.99  unif_index_add_time:                    0.
% 11.61/1.99  orderings_time:                         0.
% 11.61/1.99  out_proof_time:                         0.015
% 11.61/1.99  total_time:                             1.106
% 11.61/1.99  num_of_symbols:                         49
% 11.61/1.99  num_of_terms:                           49304
% 11.61/1.99  
% 11.61/1.99  ------ Preprocessing
% 11.61/1.99  
% 11.61/1.99  num_of_splits:                          0
% 11.61/1.99  num_of_split_atoms:                     0
% 11.61/1.99  num_of_reused_defs:                     0
% 11.61/1.99  num_eq_ax_congr_red:                    45
% 11.61/1.99  num_of_sem_filtered_clauses:            3
% 11.61/1.99  num_of_subtypes:                        3
% 11.61/1.99  monotx_restored_types:                  0
% 11.61/1.99  sat_num_of_epr_types:                   0
% 11.61/1.99  sat_num_of_non_cyclic_types:            0
% 11.61/1.99  sat_guarded_non_collapsed_types:        1
% 11.61/1.99  num_pure_diseq_elim:                    0
% 11.61/1.99  simp_replaced_by:                       0
% 11.61/1.99  res_preprocessed:                       112
% 11.61/1.99  prep_upred:                             0
% 11.61/1.99  prep_unflattend:                        20
% 11.61/1.99  smt_new_axioms:                         0
% 11.61/1.99  pred_elim_cands:                        2
% 11.61/1.99  pred_elim:                              5
% 11.61/1.99  pred_elim_cl:                           5
% 11.61/1.99  pred_elim_cycles:                       7
% 11.61/1.99  merged_defs:                            0
% 11.61/1.99  merged_defs_ncl:                        0
% 11.61/1.99  bin_hyper_res:                          0
% 11.61/1.99  prep_cycles:                            4
% 11.61/1.99  pred_elim_time:                         0.009
% 11.61/1.99  splitting_time:                         0.
% 11.61/1.99  sem_filter_time:                        0.
% 11.61/1.99  monotx_time:                            0.
% 11.61/1.99  subtype_inf_time:                       0.
% 11.61/1.99  
% 11.61/1.99  ------ Problem properties
% 11.61/1.99  
% 11.61/1.99  clauses:                                23
% 11.61/1.99  conjectures:                            3
% 11.61/1.99  epr:                                    0
% 11.61/1.99  horn:                                   17
% 11.61/1.99  ground:                                 3
% 11.61/1.99  unary:                                  3
% 11.61/1.99  binary:                                 0
% 11.61/1.99  lits:                                   107
% 11.61/1.99  lits_eq:                                13
% 11.61/1.99  fd_pure:                                0
% 11.61/1.99  fd_pseudo:                              0
% 11.61/1.99  fd_cond:                                0
% 11.61/1.99  fd_pseudo_cond:                         8
% 11.61/1.99  ac_symbols:                             0
% 11.61/1.99  
% 11.61/1.99  ------ Propositional Solver
% 11.61/1.99  
% 11.61/1.99  prop_solver_calls:                      30
% 11.61/1.99  prop_fast_solver_calls:                 1863
% 11.61/1.99  smt_solver_calls:                       0
% 11.61/1.99  smt_fast_solver_calls:                  0
% 11.61/1.99  prop_num_of_clauses:                    11610
% 11.61/1.99  prop_preprocess_simplified:             27850
% 11.61/1.99  prop_fo_subsumed:                       64
% 11.61/1.99  prop_solver_time:                       0.
% 11.61/1.99  smt_solver_time:                        0.
% 11.61/1.99  smt_fast_solver_time:                   0.
% 11.61/1.99  prop_fast_solver_time:                  0.
% 11.61/1.99  prop_unsat_core_time:                   0.001
% 11.61/1.99  
% 11.61/1.99  ------ QBF
% 11.61/1.99  
% 11.61/1.99  qbf_q_res:                              0
% 11.61/1.99  qbf_num_tautologies:                    0
% 11.61/1.99  qbf_prep_cycles:                        0
% 11.61/1.99  
% 11.61/1.99  ------ BMC1
% 11.61/1.99  
% 11.61/1.99  bmc1_current_bound:                     -1
% 11.61/1.99  bmc1_last_solved_bound:                 -1
% 11.61/1.99  bmc1_unsat_core_size:                   -1
% 11.61/1.99  bmc1_unsat_core_parents_size:           -1
% 11.61/1.99  bmc1_merge_next_fun:                    0
% 11.61/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.61/1.99  
% 11.61/1.99  ------ Instantiation
% 11.61/1.99  
% 11.61/1.99  inst_num_of_clauses:                    3444
% 11.61/1.99  inst_num_in_passive:                    1498
% 11.61/1.99  inst_num_in_active:                     785
% 11.61/1.99  inst_num_in_unprocessed:                1161
% 11.61/1.99  inst_num_of_loops:                      970
% 11.61/1.99  inst_num_of_learning_restarts:          0
% 11.61/1.99  inst_num_moves_active_passive:          183
% 11.61/1.99  inst_lit_activity:                      0
% 11.61/1.99  inst_lit_activity_moves:                1
% 11.61/1.99  inst_num_tautologies:                   0
% 11.61/1.99  inst_num_prop_implied:                  0
% 11.61/1.99  inst_num_existing_simplified:           0
% 11.61/1.99  inst_num_eq_res_simplified:             0
% 11.61/1.99  inst_num_child_elim:                    0
% 11.61/1.99  inst_num_of_dismatching_blockings:      3123
% 11.61/1.99  inst_num_of_non_proper_insts:           2256
% 11.61/1.99  inst_num_of_duplicates:                 0
% 11.61/1.99  inst_inst_num_from_inst_to_res:         0
% 11.61/1.99  inst_dismatching_checking_time:         0.
% 11.61/1.99  
% 11.61/1.99  ------ Resolution
% 11.61/1.99  
% 11.61/1.99  res_num_of_clauses:                     0
% 11.61/1.99  res_num_in_passive:                     0
% 11.61/1.99  res_num_in_active:                      0
% 11.61/1.99  res_num_of_loops:                       116
% 11.61/1.99  res_forward_subset_subsumed:            48
% 11.61/1.99  res_backward_subset_subsumed:           0
% 11.61/1.99  res_forward_subsumed:                   0
% 11.61/1.99  res_backward_subsumed:                  0
% 11.61/1.99  res_forward_subsumption_resolution:     0
% 11.61/1.99  res_backward_subsumption_resolution:    0
% 11.61/1.99  res_clause_to_clause_subsumption:       3946
% 11.61/1.99  res_orphan_elimination:                 0
% 11.61/1.99  res_tautology_del:                      77
% 11.61/1.99  res_num_eq_res_simplified:              0
% 11.61/1.99  res_num_sel_changes:                    0
% 11.61/1.99  res_moves_from_active_to_pass:          0
% 11.61/1.99  
% 11.61/1.99  ------ Superposition
% 11.61/1.99  
% 11.61/1.99  sup_time_total:                         0.
% 11.61/1.99  sup_time_generating:                    0.
% 11.61/1.99  sup_time_sim_full:                      0.
% 11.61/1.99  sup_time_sim_immed:                     0.
% 11.61/1.99  
% 11.61/1.99  sup_num_of_clauses:                     617
% 11.61/1.99  sup_num_in_active:                      173
% 11.61/1.99  sup_num_in_passive:                     444
% 11.61/1.99  sup_num_of_loops:                       192
% 11.61/1.99  sup_fw_superposition:                   433
% 11.61/1.99  sup_bw_superposition:                   247
% 11.61/1.99  sup_immediate_simplified:               229
% 11.61/1.99  sup_given_eliminated:                   0
% 11.61/1.99  comparisons_done:                       0
% 11.61/1.99  comparisons_avoided:                    0
% 11.61/1.99  
% 11.61/1.99  ------ Simplifications
% 11.61/1.99  
% 11.61/1.99  
% 11.61/1.99  sim_fw_subset_subsumed:                 12
% 11.61/1.99  sim_bw_subset_subsumed:                 3
% 11.61/1.99  sim_fw_subsumed:                        25
% 11.61/1.99  sim_bw_subsumed:                        0
% 11.61/1.99  sim_fw_subsumption_res:                 0
% 11.61/1.99  sim_bw_subsumption_res:                 1
% 11.61/1.99  sim_tautology_del:                      8
% 11.61/1.99  sim_eq_tautology_del:                   2
% 11.61/1.99  sim_eq_res_simp:                        0
% 11.61/1.99  sim_fw_demodulated:                     4
% 11.61/1.99  sim_bw_demodulated:                     18
% 11.61/1.99  sim_light_normalised:                   212
% 11.61/1.99  sim_joinable_taut:                      0
% 11.61/1.99  sim_joinable_simp:                      0
% 11.61/1.99  sim_ac_normalised:                      0
% 11.61/1.99  sim_smt_subsumption:                    0
% 11.61/1.99  
%------------------------------------------------------------------------------
