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
% DateTime   : Thu Dec  3 12:19:03 EST 2020

% Result     : Theorem 8.00s
% Output     : CNFRefutation 8.00s
% Verified   : 
% Statistics : Number of formulae       :  210 (1055 expanded)
%              Number of clauses        :  138 ( 291 expanded)
%              Number of leaves         :   20 ( 309 expanded)
%              Depth                    :   21
%              Number of atoms          : 1137 (6953 expanded)
%              Number of equality atoms :  198 (1031 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   21 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,sK4)) != X1
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
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
              ( k12_lattice3(sK2,X1,k13_lattice3(sK2,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_orders_2(sK2)
      & v2_lattice3(sK2)
      & v1_lattice3(sK2)
      & v5_orders_2(sK2)
      & v3_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_orders_2(sK2)
    & v2_lattice3(sK2)
    & v1_lattice3(sK2)
    & v5_orders_2(sK2)
    & v3_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f37,f50,f49,f48])).

fof(f79,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f51])).

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
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f41,plain,(
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

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f77,plain,(
    v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f76,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f80,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f51])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f78,plain,(
    v2_lattice3(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f11,axiom,(
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

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f75,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f58,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f58])).

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
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

fof(f46,plain,(
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

fof(f47,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f45,f46])).

fof(f66,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X5,X3)
      | ~ r1_orders_2(X0,X5,X2)
      | ~ r1_orders_2(X0,X5,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f86,plain,(
    ! [X2,X0,X5,X1] :
      ( r1_orders_2(X0,X5,k11_lattice3(X0,X1,X2))
      | ~ r1_orders_2(X0,X5,X2)
      | ~ r1_orders_2(X0,X5,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r1_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f81,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f51])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X1)
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f82,plain,(
    k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k10_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_26,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1054,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k10_lattice3(X1,X2,X0),u1_struct_0(X1))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_26])).

cnf(c_1055,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_1054])).

cnf(c_11,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1,plain,
    ( ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_216,plain,
    ( ~ v1_lattice3(X0)
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_1])).

cnf(c_217,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_216])).

cnf(c_28,negated_conjecture,
    ( v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_606,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_217,c_28])).

cnf(c_607,plain,
    ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_606])).

cnf(c_29,negated_conjecture,
    ( v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_609,plain,
    ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_607,c_29,c_26])).

cnf(c_610,plain,
    ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_609])).

cnf(c_1087,plain,
    ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1055,c_610])).

cnf(c_1248,plain,
    ( r1_orders_2(sK2,X0_47,k10_lattice3(sK2,X0_47,X1_47))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_1087])).

cnf(c_24920,plain,
    ( r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK4))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1248])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1268,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1663,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1268])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1039,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_26])).

cnf(c_1040,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(k11_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_1039])).

cnf(c_1254,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | m1_subset_1(k11_lattice3(sK2,X0_47,X1_47),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_1040])).

cnf(c_1677,plain,
    ( m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k11_lattice3(sK2,X0_47,X1_47),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1254])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k13_lattice3(X1,X2,X0) = k10_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_626,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k13_lattice3(X1,X2,X0) = k10_lattice3(X1,X2,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_28])).

cnf(c_627,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k13_lattice3(sK2,X0,X1) = k10_lattice3(sK2,X0,X1) ),
    inference(unflattening,[status(thm)],[c_626])).

cnf(c_631,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k13_lattice3(sK2,X0,X1) = k10_lattice3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_627,c_29,c_26])).

cnf(c_1262,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | k13_lattice3(sK2,X0_47,X1_47) = k10_lattice3(sK2,X0_47,X1_47) ),
    inference(subtyping,[status(esa)],[c_631])).

cnf(c_1669,plain,
    ( k13_lattice3(sK2,X0_47,X1_47) = k10_lattice3(sK2,X0_47,X1_47)
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1262])).

cnf(c_2447,plain,
    ( k13_lattice3(sK2,k11_lattice3(sK2,X0_47,X1_47),X2_47) = k10_lattice3(sK2,k11_lattice3(sK2,X0_47,X1_47),X2_47)
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_47,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1677,c_1669])).

cnf(c_17026,plain,
    ( k13_lattice3(sK2,k11_lattice3(sK2,sK3,X0_47),X1_47) = k10_lattice3(sK2,k11_lattice3(sK2,sK3,X0_47),X1_47)
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1663,c_2447])).

cnf(c_18096,plain,
    ( k13_lattice3(sK2,k11_lattice3(sK2,sK3,sK3),X0_47) = k10_lattice3(sK2,k11_lattice3(sK2,sK3,sK3),X0_47)
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1663,c_17026])).

cnf(c_18282,plain,
    ( k13_lattice3(sK2,k11_lattice3(sK2,sK3,sK3),sK3) = k10_lattice3(sK2,k11_lattice3(sK2,sK3,sK3),sK3) ),
    inference(superposition,[status(thm)],[c_1663,c_18096])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_27,negated_conjecture,
    ( v2_lattice3(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_927,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_27])).

cnf(c_928,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k12_lattice3(sK2,X0,X1) = k11_lattice3(sK2,X0,X1) ),
    inference(unflattening,[status(thm)],[c_927])).

cnf(c_932,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k12_lattice3(sK2,X0,X1) = k11_lattice3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_928,c_29,c_26])).

cnf(c_1256,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | k12_lattice3(sK2,X0_47,X1_47) = k11_lattice3(sK2,X0_47,X1_47) ),
    inference(subtyping,[status(esa)],[c_932])).

cnf(c_1675,plain,
    ( k12_lattice3(sK2,X0_47,X1_47) = k11_lattice3(sK2,X0_47,X1_47)
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1256])).

cnf(c_5504,plain,
    ( k12_lattice3(sK2,sK3,X0_47) = k11_lattice3(sK2,sK3,X0_47)
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1663,c_1675])).

cnf(c_5604,plain,
    ( k12_lattice3(sK2,sK3,sK3) = k11_lattice3(sK2,sK3,sK3) ),
    inference(superposition,[status(thm)],[c_1663,c_5504])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k13_lattice3(X1,k12_lattice3(X1,X2,X0),X0) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_30,negated_conjecture,
    ( v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_396,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k13_lattice3(X1,k12_lattice3(X1,X2,X0),X0) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_30])).

cnf(c_397,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v2_lattice3(sK2)
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k13_lattice3(sK2,k12_lattice3(sK2,X0,X1),X1) = X1 ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_401,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k13_lattice3(sK2,k12_lattice3(sK2,X0,X1),X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_397,c_29,c_28,c_27,c_26])).

cnf(c_1267,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | k13_lattice3(sK2,k12_lattice3(sK2,X0_47,X1_47),X1_47) = X1_47 ),
    inference(subtyping,[status(esa)],[c_401])).

cnf(c_1664,plain,
    ( k13_lattice3(sK2,k12_lattice3(sK2,X0_47,X1_47),X1_47) = X1_47
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1267])).

cnf(c_1811,plain,
    ( k13_lattice3(sK2,k12_lattice3(sK2,sK3,X0_47),X0_47) = X0_47
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1663,c_1664])).

cnf(c_2152,plain,
    ( k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK3),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_1663,c_1811])).

cnf(c_5683,plain,
    ( k13_lattice3(sK2,k11_lattice3(sK2,sK3,sK3),sK3) = sK3 ),
    inference(demodulation,[status(thm)],[c_5604,c_2152])).

cnf(c_18287,plain,
    ( k10_lattice3(sK2,k11_lattice3(sK2,sK3,sK3),sK3) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_18282,c_5683])).

cnf(c_10,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_223,plain,
    ( ~ v1_lattice3(X0)
    | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_1])).

cnf(c_224,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_223])).

cnf(c_582,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_224,c_28])).

cnf(c_583,plain,
    ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X1,X0),u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_582])).

cnf(c_587,plain,
    ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X1,X0),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_583,c_29,c_26])).

cnf(c_588,plain,
    ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X1,X0),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_587])).

cnf(c_1088,plain,
    ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1055,c_588])).

cnf(c_1247,plain,
    ( r1_orders_2(sK2,X0_47,k10_lattice3(sK2,X1_47,X0_47))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_1088])).

cnf(c_1684,plain,
    ( r1_orders_2(sK2,X0_47,k10_lattice3(sK2,X1_47,X0_47)) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1247])).

cnf(c_18528,plain,
    ( r1_orders_2(sK2,sK3,sK3) = iProver_top
    | m1_subset_1(k11_lattice3(sK2,sK3,sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18287,c_1684])).

cnf(c_1274,plain,
    ( ~ r1_orders_2(X0_46,X0_47,X1_47)
    | r1_orders_2(X0_46,X2_47,X3_47)
    | X2_47 != X0_47
    | X3_47 != X1_47 ),
    theory(equality)).

cnf(c_1736,plain,
    ( ~ r1_orders_2(sK2,X0_47,X1_47)
    | r1_orders_2(sK2,X2_47,X3_47)
    | X2_47 != X0_47
    | X3_47 != X1_47 ),
    inference(instantiation,[status(thm)],[c_1274])).

cnf(c_1915,plain,
    ( r1_orders_2(sK2,X0_47,X1_47)
    | ~ r1_orders_2(sK2,X2_47,k10_lattice3(sK2,X2_47,X3_47))
    | X0_47 != X2_47
    | X1_47 != k10_lattice3(sK2,X2_47,X3_47) ),
    inference(instantiation,[status(thm)],[c_1736])).

cnf(c_2379,plain,
    ( r1_orders_2(sK2,X0_47,k13_lattice3(sK2,X1_47,X2_47))
    | ~ r1_orders_2(sK2,X1_47,k10_lattice3(sK2,X1_47,X2_47))
    | X0_47 != X1_47
    | k13_lattice3(sK2,X1_47,X2_47) != k10_lattice3(sK2,X1_47,X2_47) ),
    inference(instantiation,[status(thm)],[c_1915])).

cnf(c_7439,plain,
    ( r1_orders_2(sK2,X0_47,k13_lattice3(sK2,sK3,sK4))
    | ~ r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK4))
    | X0_47 != sK3
    | k13_lattice3(sK2,sK3,sK4) != k10_lattice3(sK2,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2379])).

cnf(c_7446,plain,
    ( r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
    | ~ r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK4))
    | k13_lattice3(sK2,sK3,sK4) != k10_lattice3(sK2,sK3,sK4)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_7439])).

cnf(c_16,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,X1,k11_lattice3(X0,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X3,X2),u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2,plain,
    ( ~ v2_lattice3(X0)
    | ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_183,plain,
    ( ~ v2_lattice3(X0)
    | ~ m1_subset_1(k11_lattice3(X0,X3,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,X1,k11_lattice3(X0,X3,X2))
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_2])).

cnf(c_184,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,X1,k11_lattice3(X0,X3,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X3,X2),u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_183])).

cnf(c_829,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,X1,k11_lattice3(X0,X3,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X3,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_184,c_27])).

cnf(c_830,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | r1_orders_2(sK2,X0,k11_lattice3(sK2,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(k11_lattice3(sK2,X2,X1),u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_829])).

cnf(c_834,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | r1_orders_2(sK2,X0,k11_lattice3(sK2,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(k11_lattice3(sK2,X2,X1),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_830,c_29,c_26])).

cnf(c_835,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | r1_orders_2(sK2,X0,k11_lattice3(sK2,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(k11_lattice3(sK2,X2,X1),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_834])).

cnf(c_1072,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | r1_orders_2(sK2,X0,k11_lattice3(sK2,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1040,c_835])).

cnf(c_1252,plain,
    ( ~ r1_orders_2(sK2,X0_47,X1_47)
    | ~ r1_orders_2(sK2,X0_47,X2_47)
    | r1_orders_2(sK2,X0_47,k11_lattice3(sK2,X2_47,X1_47))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X2_47,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_1072])).

cnf(c_2852,plain,
    ( ~ r1_orders_2(sK2,X0_47,X1_47)
    | ~ r1_orders_2(sK2,X0_47,k13_lattice3(sK2,X2_47,X3_47))
    | r1_orders_2(sK2,X0_47,k11_lattice3(sK2,X1_47,k13_lattice3(sK2,X2_47,X3_47)))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | ~ m1_subset_1(k13_lattice3(sK2,X2_47,X3_47),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1252])).

cnf(c_7117,plain,
    ( ~ r1_orders_2(sK2,X0_47,X1_47)
    | ~ r1_orders_2(sK2,X0_47,k13_lattice3(sK2,sK3,sK4))
    | r1_orders_2(sK2,X0_47,k11_lattice3(sK2,X1_47,k13_lattice3(sK2,sK3,sK4)))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2852])).

cnf(c_7147,plain,
    ( ~ r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
    | r1_orders_2(sK2,sK3,k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)))
    | ~ r1_orders_2(sK2,sK3,sK3)
    | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_7117])).

cnf(c_4306,plain,
    ( ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | m1_subset_1(k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1254])).

cnf(c_1253,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | m1_subset_1(k10_lattice3(sK2,X0_47,X1_47),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_1055])).

cnf(c_4295,plain,
    ( m1_subset_1(k10_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1253])).

cnf(c_1275,plain,
    ( ~ m1_subset_1(X0_47,X0_48)
    | m1_subset_1(X1_47,X0_48)
    | X1_47 != X0_47 ),
    theory(equality)).

cnf(c_2132,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | k13_lattice3(sK2,sK3,sK4) != X0_47 ),
    inference(instantiation,[status(thm)],[c_1275])).

cnf(c_3685,plain,
    ( m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | k13_lattice3(sK2,sK3,sK4) != k10_lattice3(sK2,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2132])).

cnf(c_0,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | X1 = X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1006,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | X2 = X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_29])).

cnf(c_1007,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_1006])).

cnf(c_1011,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r1_orders_2(sK2,X1,X0)
    | ~ r1_orders_2(sK2,X0,X1)
    | X1 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1007,c_26])).

cnf(c_1012,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | X1 = X0 ),
    inference(renaming,[status(thm)],[c_1011])).

cnf(c_1255,plain,
    ( ~ r1_orders_2(sK2,X0_47,X1_47)
    | ~ r1_orders_2(sK2,X1_47,X0_47)
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | X1_47 = X0_47 ),
    inference(subtyping,[status(esa)],[c_1012])).

cnf(c_3655,plain,
    ( ~ r1_orders_2(sK2,X0_47,k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)))
    | ~ r1_orders_2(sK2,k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)),X0_47)
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)),u1_struct_0(sK2))
    | k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_47 ),
    inference(instantiation,[status(thm)],[c_1255])).

cnf(c_3657,plain,
    ( ~ r1_orders_2(sK2,k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)),sK3)
    | ~ r1_orders_2(sK2,sK3,k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)))
    | ~ m1_subset_1(k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3 ),
    inference(instantiation,[status(thm)],[c_3655])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1269,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1662,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1269])).

cnf(c_2445,plain,
    ( k13_lattice3(sK2,sK3,X0_47) = k10_lattice3(sK2,sK3,X0_47)
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1663,c_1669])).

cnf(c_3407,plain,
    ( k13_lattice3(sK2,sK3,sK4) = k10_lattice3(sK2,sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1662,c_2445])).

cnf(c_18,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_171,plain,
    ( ~ v2_lattice3(X0)
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_2])).

cnf(c_172,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_171])).

cnf(c_886,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_172,c_27])).

cnf(c_887,plain,
    ( r1_orders_2(sK2,k11_lattice3(sK2,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(k11_lattice3(sK2,X0,X1),u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_886])).

cnf(c_889,plain,
    ( r1_orders_2(sK2,k11_lattice3(sK2,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(k11_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_887,c_29,c_26])).

cnf(c_890,plain,
    ( r1_orders_2(sK2,k11_lattice3(sK2,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(k11_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_889])).

cnf(c_1073,plain,
    ( r1_orders_2(sK2,k11_lattice3(sK2,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1040,c_890])).

cnf(c_1251,plain,
    ( r1_orders_2(sK2,k11_lattice3(sK2,X0_47,X1_47),X0_47)
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_1073])).

cnf(c_2772,plain,
    ( r1_orders_2(sK2,k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)),sK3)
    | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1251])).

cnf(c_2396,plain,
    ( ~ r1_orders_2(sK2,X0_47,k11_lattice3(sK2,X1_47,X2_47))
    | ~ r1_orders_2(sK2,k11_lattice3(sK2,X1_47,X2_47),X0_47)
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(k11_lattice3(sK2,X1_47,X2_47),u1_struct_0(sK2))
    | X0_47 = k11_lattice3(sK2,X1_47,X2_47) ),
    inference(instantiation,[status(thm)],[c_1255])).

cnf(c_2397,plain,
    ( X0_47 = k11_lattice3(sK2,X1_47,X2_47)
    | r1_orders_2(sK2,X0_47,k11_lattice3(sK2,X1_47,X2_47)) != iProver_top
    | r1_orders_2(sK2,k11_lattice3(sK2,X1_47,X2_47),X0_47) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k11_lattice3(sK2,X1_47,X2_47),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2396])).

cnf(c_2399,plain,
    ( sK3 = k11_lattice3(sK2,sK3,sK3)
    | r1_orders_2(sK2,k11_lattice3(sK2,sK3,sK3),sK3) != iProver_top
    | r1_orders_2(sK2,sK3,k11_lattice3(sK2,sK3,sK3)) != iProver_top
    | m1_subset_1(k11_lattice3(sK2,sK3,sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2397])).

cnf(c_1273,plain,
    ( X0_47 != X1_47
    | X2_47 != X1_47
    | X2_47 = X0_47 ),
    theory(equality)).

cnf(c_2130,plain,
    ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != X0_47
    | sK3 != X0_47
    | sK3 = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1273])).

cnf(c_2131,plain,
    ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3
    | sK3 = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2130])).

cnf(c_1918,plain,
    ( r1_orders_2(sK2,X0_47,X1_47)
    | ~ r1_orders_2(sK2,k11_lattice3(sK2,X2_47,X3_47),X3_47)
    | X1_47 != X3_47
    | X0_47 != k11_lattice3(sK2,X2_47,X3_47) ),
    inference(instantiation,[status(thm)],[c_1736])).

cnf(c_1920,plain,
    ( ~ r1_orders_2(sK2,k11_lattice3(sK2,sK3,sK3),sK3)
    | r1_orders_2(sK2,sK3,sK3)
    | sK3 != k11_lattice3(sK2,sK3,sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1918])).

cnf(c_1879,plain,
    ( ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1256])).

cnf(c_1731,plain,
    ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != X0_47
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
    | sK3 != X0_47 ),
    inference(instantiation,[status(thm)],[c_1273])).

cnf(c_1878,plain,
    ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
    | sK3 != k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1731])).

cnf(c_1328,plain,
    ( r1_orders_2(sK2,k11_lattice3(sK2,X0_47,X1_47),X0_47) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1251])).

cnf(c_1330,plain,
    ( r1_orders_2(sK2,k11_lattice3(sK2,sK3,sK3),sK3) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1328])).

cnf(c_1329,plain,
    ( r1_orders_2(sK2,k11_lattice3(sK2,sK3,sK3),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1251])).

cnf(c_1325,plain,
    ( r1_orders_2(sK2,X0_47,X1_47) != iProver_top
    | r1_orders_2(sK2,X0_47,X2_47) != iProver_top
    | r1_orders_2(sK2,X0_47,k11_lattice3(sK2,X1_47,X2_47)) = iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1252])).

cnf(c_1327,plain,
    ( r1_orders_2(sK2,sK3,k11_lattice3(sK2,sK3,sK3)) = iProver_top
    | r1_orders_2(sK2,sK3,sK3) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1325])).

cnf(c_1319,plain,
    ( m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k11_lattice3(sK2,X0_47,X1_47),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1254])).

cnf(c_1321,plain,
    ( m1_subset_1(k11_lattice3(sK2,sK3,sK3),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1319])).

cnf(c_23,negated_conjecture,
    ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1270,negated_conjecture,
    ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1272,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_1283,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1272])).

cnf(c_36,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_24920,c_18528,c_7446,c_7147,c_4306,c_4295,c_3685,c_3657,c_3407,c_2772,c_2399,c_2131,c_1920,c_1879,c_1878,c_1330,c_1329,c_1327,c_1321,c_1270,c_1283,c_24,c_36,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:25:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 8.00/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.00/1.50  
% 8.00/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.00/1.50  
% 8.00/1.50  ------  iProver source info
% 8.00/1.50  
% 8.00/1.50  git: date: 2020-06-30 10:37:57 +0100
% 8.00/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.00/1.50  git: non_committed_changes: false
% 8.00/1.50  git: last_make_outside_of_git: false
% 8.00/1.50  
% 8.00/1.50  ------ 
% 8.00/1.50  
% 8.00/1.50  ------ Input Options
% 8.00/1.50  
% 8.00/1.50  --out_options                           all
% 8.00/1.50  --tptp_safe_out                         true
% 8.00/1.50  --problem_path                          ""
% 8.00/1.50  --include_path                          ""
% 8.00/1.50  --clausifier                            res/vclausify_rel
% 8.00/1.50  --clausifier_options                    ""
% 8.00/1.50  --stdin                                 false
% 8.00/1.50  --stats_out                             all
% 8.00/1.50  
% 8.00/1.50  ------ General Options
% 8.00/1.50  
% 8.00/1.50  --fof                                   false
% 8.00/1.50  --time_out_real                         305.
% 8.00/1.50  --time_out_virtual                      -1.
% 8.00/1.50  --symbol_type_check                     false
% 8.00/1.50  --clausify_out                          false
% 8.00/1.50  --sig_cnt_out                           false
% 8.00/1.50  --trig_cnt_out                          false
% 8.00/1.50  --trig_cnt_out_tolerance                1.
% 8.00/1.50  --trig_cnt_out_sk_spl                   false
% 8.00/1.50  --abstr_cl_out                          false
% 8.00/1.50  
% 8.00/1.50  ------ Global Options
% 8.00/1.50  
% 8.00/1.50  --schedule                              default
% 8.00/1.50  --add_important_lit                     false
% 8.00/1.50  --prop_solver_per_cl                    1000
% 8.00/1.50  --min_unsat_core                        false
% 8.00/1.50  --soft_assumptions                      false
% 8.00/1.50  --soft_lemma_size                       3
% 8.00/1.50  --prop_impl_unit_size                   0
% 8.00/1.50  --prop_impl_unit                        []
% 8.00/1.50  --share_sel_clauses                     true
% 8.00/1.50  --reset_solvers                         false
% 8.00/1.50  --bc_imp_inh                            [conj_cone]
% 8.00/1.50  --conj_cone_tolerance                   3.
% 8.00/1.50  --extra_neg_conj                        none
% 8.00/1.50  --large_theory_mode                     true
% 8.00/1.50  --prolific_symb_bound                   200
% 8.00/1.50  --lt_threshold                          2000
% 8.00/1.50  --clause_weak_htbl                      true
% 8.00/1.50  --gc_record_bc_elim                     false
% 8.00/1.50  
% 8.00/1.50  ------ Preprocessing Options
% 8.00/1.50  
% 8.00/1.50  --preprocessing_flag                    true
% 8.00/1.50  --time_out_prep_mult                    0.1
% 8.00/1.50  --splitting_mode                        input
% 8.00/1.50  --splitting_grd                         true
% 8.00/1.50  --splitting_cvd                         false
% 8.00/1.50  --splitting_cvd_svl                     false
% 8.00/1.50  --splitting_nvd                         32
% 8.00/1.50  --sub_typing                            true
% 8.00/1.50  --prep_gs_sim                           true
% 8.00/1.50  --prep_unflatten                        true
% 8.00/1.50  --prep_res_sim                          true
% 8.00/1.50  --prep_upred                            true
% 8.00/1.50  --prep_sem_filter                       exhaustive
% 8.00/1.50  --prep_sem_filter_out                   false
% 8.00/1.50  --pred_elim                             true
% 8.00/1.50  --res_sim_input                         true
% 8.00/1.50  --eq_ax_congr_red                       true
% 8.00/1.50  --pure_diseq_elim                       true
% 8.00/1.50  --brand_transform                       false
% 8.00/1.50  --non_eq_to_eq                          false
% 8.00/1.50  --prep_def_merge                        true
% 8.00/1.50  --prep_def_merge_prop_impl              false
% 8.00/1.50  --prep_def_merge_mbd                    true
% 8.00/1.50  --prep_def_merge_tr_red                 false
% 8.00/1.50  --prep_def_merge_tr_cl                  false
% 8.00/1.50  --smt_preprocessing                     true
% 8.00/1.50  --smt_ac_axioms                         fast
% 8.00/1.50  --preprocessed_out                      false
% 8.00/1.50  --preprocessed_stats                    false
% 8.00/1.50  
% 8.00/1.50  ------ Abstraction refinement Options
% 8.00/1.50  
% 8.00/1.50  --abstr_ref                             []
% 8.00/1.50  --abstr_ref_prep                        false
% 8.00/1.50  --abstr_ref_until_sat                   false
% 8.00/1.50  --abstr_ref_sig_restrict                funpre
% 8.00/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 8.00/1.50  --abstr_ref_under                       []
% 8.00/1.50  
% 8.00/1.50  ------ SAT Options
% 8.00/1.50  
% 8.00/1.50  --sat_mode                              false
% 8.00/1.50  --sat_fm_restart_options                ""
% 8.00/1.50  --sat_gr_def                            false
% 8.00/1.50  --sat_epr_types                         true
% 8.00/1.50  --sat_non_cyclic_types                  false
% 8.00/1.50  --sat_finite_models                     false
% 8.00/1.50  --sat_fm_lemmas                         false
% 8.00/1.50  --sat_fm_prep                           false
% 8.00/1.50  --sat_fm_uc_incr                        true
% 8.00/1.50  --sat_out_model                         small
% 8.00/1.50  --sat_out_clauses                       false
% 8.00/1.50  
% 8.00/1.50  ------ QBF Options
% 8.00/1.50  
% 8.00/1.50  --qbf_mode                              false
% 8.00/1.50  --qbf_elim_univ                         false
% 8.00/1.50  --qbf_dom_inst                          none
% 8.00/1.50  --qbf_dom_pre_inst                      false
% 8.00/1.50  --qbf_sk_in                             false
% 8.00/1.50  --qbf_pred_elim                         true
% 8.00/1.50  --qbf_split                             512
% 8.00/1.50  
% 8.00/1.50  ------ BMC1 Options
% 8.00/1.50  
% 8.00/1.50  --bmc1_incremental                      false
% 8.00/1.50  --bmc1_axioms                           reachable_all
% 8.00/1.50  --bmc1_min_bound                        0
% 8.00/1.50  --bmc1_max_bound                        -1
% 8.00/1.50  --bmc1_max_bound_default                -1
% 8.00/1.50  --bmc1_symbol_reachability              true
% 8.00/1.50  --bmc1_property_lemmas                  false
% 8.00/1.50  --bmc1_k_induction                      false
% 8.00/1.50  --bmc1_non_equiv_states                 false
% 8.00/1.50  --bmc1_deadlock                         false
% 8.00/1.50  --bmc1_ucm                              false
% 8.00/1.50  --bmc1_add_unsat_core                   none
% 8.00/1.50  --bmc1_unsat_core_children              false
% 8.00/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 8.00/1.50  --bmc1_out_stat                         full
% 8.00/1.50  --bmc1_ground_init                      false
% 8.00/1.50  --bmc1_pre_inst_next_state              false
% 8.00/1.50  --bmc1_pre_inst_state                   false
% 8.00/1.50  --bmc1_pre_inst_reach_state             false
% 8.00/1.50  --bmc1_out_unsat_core                   false
% 8.00/1.50  --bmc1_aig_witness_out                  false
% 8.00/1.50  --bmc1_verbose                          false
% 8.00/1.50  --bmc1_dump_clauses_tptp                false
% 8.00/1.50  --bmc1_dump_unsat_core_tptp             false
% 8.00/1.50  --bmc1_dump_file                        -
% 8.00/1.50  --bmc1_ucm_expand_uc_limit              128
% 8.00/1.50  --bmc1_ucm_n_expand_iterations          6
% 8.00/1.50  --bmc1_ucm_extend_mode                  1
% 8.00/1.50  --bmc1_ucm_init_mode                    2
% 8.00/1.50  --bmc1_ucm_cone_mode                    none
% 8.00/1.50  --bmc1_ucm_reduced_relation_type        0
% 8.00/1.50  --bmc1_ucm_relax_model                  4
% 8.00/1.50  --bmc1_ucm_full_tr_after_sat            true
% 8.00/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 8.00/1.50  --bmc1_ucm_layered_model                none
% 8.00/1.50  --bmc1_ucm_max_lemma_size               10
% 8.00/1.50  
% 8.00/1.50  ------ AIG Options
% 8.00/1.50  
% 8.00/1.50  --aig_mode                              false
% 8.00/1.50  
% 8.00/1.50  ------ Instantiation Options
% 8.00/1.50  
% 8.00/1.50  --instantiation_flag                    true
% 8.00/1.50  --inst_sos_flag                         true
% 8.00/1.50  --inst_sos_phase                        true
% 8.00/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.00/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.00/1.50  --inst_lit_sel_side                     num_symb
% 8.00/1.50  --inst_solver_per_active                1400
% 8.00/1.50  --inst_solver_calls_frac                1.
% 8.00/1.50  --inst_passive_queue_type               priority_queues
% 8.00/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.00/1.50  --inst_passive_queues_freq              [25;2]
% 8.00/1.50  --inst_dismatching                      true
% 8.00/1.50  --inst_eager_unprocessed_to_passive     true
% 8.00/1.50  --inst_prop_sim_given                   true
% 8.00/1.50  --inst_prop_sim_new                     false
% 8.00/1.50  --inst_subs_new                         false
% 8.00/1.50  --inst_eq_res_simp                      false
% 8.00/1.50  --inst_subs_given                       false
% 8.00/1.50  --inst_orphan_elimination               true
% 8.00/1.50  --inst_learning_loop_flag               true
% 8.00/1.50  --inst_learning_start                   3000
% 8.00/1.50  --inst_learning_factor                  2
% 8.00/1.50  --inst_start_prop_sim_after_learn       3
% 8.00/1.50  --inst_sel_renew                        solver
% 8.00/1.50  --inst_lit_activity_flag                true
% 8.00/1.50  --inst_restr_to_given                   false
% 8.00/1.50  --inst_activity_threshold               500
% 8.00/1.50  --inst_out_proof                        true
% 8.00/1.50  
% 8.00/1.50  ------ Resolution Options
% 8.00/1.50  
% 8.00/1.50  --resolution_flag                       true
% 8.00/1.50  --res_lit_sel                           adaptive
% 8.00/1.50  --res_lit_sel_side                      none
% 8.00/1.50  --res_ordering                          kbo
% 8.00/1.50  --res_to_prop_solver                    active
% 8.00/1.50  --res_prop_simpl_new                    false
% 8.00/1.50  --res_prop_simpl_given                  true
% 8.00/1.50  --res_passive_queue_type                priority_queues
% 8.00/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.00/1.50  --res_passive_queues_freq               [15;5]
% 8.00/1.50  --res_forward_subs                      full
% 8.00/1.50  --res_backward_subs                     full
% 8.00/1.50  --res_forward_subs_resolution           true
% 8.00/1.50  --res_backward_subs_resolution          true
% 8.00/1.50  --res_orphan_elimination                true
% 8.00/1.50  --res_time_limit                        2.
% 8.00/1.50  --res_out_proof                         true
% 8.00/1.50  
% 8.00/1.50  ------ Superposition Options
% 8.00/1.50  
% 8.00/1.50  --superposition_flag                    true
% 8.00/1.50  --sup_passive_queue_type                priority_queues
% 8.00/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.00/1.50  --sup_passive_queues_freq               [8;1;4]
% 8.00/1.50  --demod_completeness_check              fast
% 8.00/1.50  --demod_use_ground                      true
% 8.00/1.50  --sup_to_prop_solver                    passive
% 8.00/1.50  --sup_prop_simpl_new                    true
% 8.00/1.50  --sup_prop_simpl_given                  true
% 8.00/1.50  --sup_fun_splitting                     true
% 8.00/1.50  --sup_smt_interval                      50000
% 8.00/1.50  
% 8.00/1.50  ------ Superposition Simplification Setup
% 8.00/1.50  
% 8.00/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.00/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.00/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.00/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.00/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 8.00/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.00/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.00/1.50  --sup_immed_triv                        [TrivRules]
% 8.00/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.00/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.00/1.50  --sup_immed_bw_main                     []
% 8.00/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.00/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 8.00/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.00/1.50  --sup_input_bw                          []
% 8.00/1.50  
% 8.00/1.50  ------ Combination Options
% 8.00/1.50  
% 8.00/1.50  --comb_res_mult                         3
% 8.00/1.50  --comb_sup_mult                         2
% 8.00/1.50  --comb_inst_mult                        10
% 8.00/1.50  
% 8.00/1.50  ------ Debug Options
% 8.00/1.50  
% 8.00/1.50  --dbg_backtrace                         false
% 8.00/1.50  --dbg_dump_prop_clauses                 false
% 8.00/1.50  --dbg_dump_prop_clauses_file            -
% 8.00/1.50  --dbg_out_stat                          false
% 8.00/1.50  ------ Parsing...
% 8.00/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.00/1.50  
% 8.00/1.50  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 8.00/1.50  
% 8.00/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.00/1.50  
% 8.00/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.00/1.50  ------ Proving...
% 8.00/1.50  ------ Problem Properties 
% 8.00/1.50  
% 8.00/1.50  
% 8.00/1.50  clauses                                 24
% 8.00/1.50  conjectures                             3
% 8.00/1.50  EPR                                     0
% 8.00/1.50  Horn                                    18
% 8.00/1.50  unary                                   3
% 8.00/1.50  binary                                  0
% 8.00/1.50  lits                                    106
% 8.00/1.50  lits eq                                 14
% 8.00/1.50  fd_pure                                 0
% 8.00/1.50  fd_pseudo                               0
% 8.00/1.50  fd_cond                                 0
% 8.00/1.50  fd_pseudo_cond                          9
% 8.00/1.50  AC symbols                              0
% 8.00/1.50  
% 8.00/1.50  ------ Schedule dynamic 5 is on 
% 8.00/1.50  
% 8.00/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 8.00/1.50  
% 8.00/1.50  
% 8.00/1.50  ------ 
% 8.00/1.50  Current options:
% 8.00/1.50  ------ 
% 8.00/1.50  
% 8.00/1.50  ------ Input Options
% 8.00/1.50  
% 8.00/1.50  --out_options                           all
% 8.00/1.50  --tptp_safe_out                         true
% 8.00/1.50  --problem_path                          ""
% 8.00/1.50  --include_path                          ""
% 8.00/1.50  --clausifier                            res/vclausify_rel
% 8.00/1.50  --clausifier_options                    ""
% 8.00/1.50  --stdin                                 false
% 8.00/1.50  --stats_out                             all
% 8.00/1.50  
% 8.00/1.50  ------ General Options
% 8.00/1.50  
% 8.00/1.50  --fof                                   false
% 8.00/1.50  --time_out_real                         305.
% 8.00/1.50  --time_out_virtual                      -1.
% 8.00/1.50  --symbol_type_check                     false
% 8.00/1.50  --clausify_out                          false
% 8.00/1.50  --sig_cnt_out                           false
% 8.00/1.50  --trig_cnt_out                          false
% 8.00/1.50  --trig_cnt_out_tolerance                1.
% 8.00/1.50  --trig_cnt_out_sk_spl                   false
% 8.00/1.50  --abstr_cl_out                          false
% 8.00/1.50  
% 8.00/1.50  ------ Global Options
% 8.00/1.50  
% 8.00/1.50  --schedule                              default
% 8.00/1.50  --add_important_lit                     false
% 8.00/1.50  --prop_solver_per_cl                    1000
% 8.00/1.50  --min_unsat_core                        false
% 8.00/1.50  --soft_assumptions                      false
% 8.00/1.50  --soft_lemma_size                       3
% 8.00/1.50  --prop_impl_unit_size                   0
% 8.00/1.50  --prop_impl_unit                        []
% 8.00/1.50  --share_sel_clauses                     true
% 8.00/1.50  --reset_solvers                         false
% 8.00/1.50  --bc_imp_inh                            [conj_cone]
% 8.00/1.50  --conj_cone_tolerance                   3.
% 8.00/1.50  --extra_neg_conj                        none
% 8.00/1.50  --large_theory_mode                     true
% 8.00/1.50  --prolific_symb_bound                   200
% 8.00/1.50  --lt_threshold                          2000
% 8.00/1.50  --clause_weak_htbl                      true
% 8.00/1.50  --gc_record_bc_elim                     false
% 8.00/1.50  
% 8.00/1.50  ------ Preprocessing Options
% 8.00/1.50  
% 8.00/1.50  --preprocessing_flag                    true
% 8.00/1.50  --time_out_prep_mult                    0.1
% 8.00/1.50  --splitting_mode                        input
% 8.00/1.50  --splitting_grd                         true
% 8.00/1.50  --splitting_cvd                         false
% 8.00/1.50  --splitting_cvd_svl                     false
% 8.00/1.50  --splitting_nvd                         32
% 8.00/1.50  --sub_typing                            true
% 8.00/1.50  --prep_gs_sim                           true
% 8.00/1.50  --prep_unflatten                        true
% 8.00/1.50  --prep_res_sim                          true
% 8.00/1.50  --prep_upred                            true
% 8.00/1.50  --prep_sem_filter                       exhaustive
% 8.00/1.50  --prep_sem_filter_out                   false
% 8.00/1.50  --pred_elim                             true
% 8.00/1.50  --res_sim_input                         true
% 8.00/1.50  --eq_ax_congr_red                       true
% 8.00/1.50  --pure_diseq_elim                       true
% 8.00/1.50  --brand_transform                       false
% 8.00/1.50  --non_eq_to_eq                          false
% 8.00/1.50  --prep_def_merge                        true
% 8.00/1.50  --prep_def_merge_prop_impl              false
% 8.00/1.50  --prep_def_merge_mbd                    true
% 8.00/1.50  --prep_def_merge_tr_red                 false
% 8.00/1.50  --prep_def_merge_tr_cl                  false
% 8.00/1.50  --smt_preprocessing                     true
% 8.00/1.50  --smt_ac_axioms                         fast
% 8.00/1.50  --preprocessed_out                      false
% 8.00/1.50  --preprocessed_stats                    false
% 8.00/1.50  
% 8.00/1.50  ------ Abstraction refinement Options
% 8.00/1.50  
% 8.00/1.50  --abstr_ref                             []
% 8.00/1.50  --abstr_ref_prep                        false
% 8.00/1.50  --abstr_ref_until_sat                   false
% 8.00/1.50  --abstr_ref_sig_restrict                funpre
% 8.00/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 8.00/1.50  --abstr_ref_under                       []
% 8.00/1.50  
% 8.00/1.50  ------ SAT Options
% 8.00/1.50  
% 8.00/1.50  --sat_mode                              false
% 8.00/1.50  --sat_fm_restart_options                ""
% 8.00/1.50  --sat_gr_def                            false
% 8.00/1.50  --sat_epr_types                         true
% 8.00/1.50  --sat_non_cyclic_types                  false
% 8.00/1.50  --sat_finite_models                     false
% 8.00/1.50  --sat_fm_lemmas                         false
% 8.00/1.50  --sat_fm_prep                           false
% 8.00/1.50  --sat_fm_uc_incr                        true
% 8.00/1.50  --sat_out_model                         small
% 8.00/1.50  --sat_out_clauses                       false
% 8.00/1.50  
% 8.00/1.50  ------ QBF Options
% 8.00/1.50  
% 8.00/1.50  --qbf_mode                              false
% 8.00/1.50  --qbf_elim_univ                         false
% 8.00/1.50  --qbf_dom_inst                          none
% 8.00/1.50  --qbf_dom_pre_inst                      false
% 8.00/1.50  --qbf_sk_in                             false
% 8.00/1.50  --qbf_pred_elim                         true
% 8.00/1.50  --qbf_split                             512
% 8.00/1.50  
% 8.00/1.50  ------ BMC1 Options
% 8.00/1.50  
% 8.00/1.50  --bmc1_incremental                      false
% 8.00/1.50  --bmc1_axioms                           reachable_all
% 8.00/1.50  --bmc1_min_bound                        0
% 8.00/1.50  --bmc1_max_bound                        -1
% 8.00/1.50  --bmc1_max_bound_default                -1
% 8.00/1.50  --bmc1_symbol_reachability              true
% 8.00/1.50  --bmc1_property_lemmas                  false
% 8.00/1.50  --bmc1_k_induction                      false
% 8.00/1.50  --bmc1_non_equiv_states                 false
% 8.00/1.50  --bmc1_deadlock                         false
% 8.00/1.50  --bmc1_ucm                              false
% 8.00/1.50  --bmc1_add_unsat_core                   none
% 8.00/1.50  --bmc1_unsat_core_children              false
% 8.00/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 8.00/1.50  --bmc1_out_stat                         full
% 8.00/1.50  --bmc1_ground_init                      false
% 8.00/1.50  --bmc1_pre_inst_next_state              false
% 8.00/1.50  --bmc1_pre_inst_state                   false
% 8.00/1.50  --bmc1_pre_inst_reach_state             false
% 8.00/1.50  --bmc1_out_unsat_core                   false
% 8.00/1.50  --bmc1_aig_witness_out                  false
% 8.00/1.50  --bmc1_verbose                          false
% 8.00/1.50  --bmc1_dump_clauses_tptp                false
% 8.00/1.50  --bmc1_dump_unsat_core_tptp             false
% 8.00/1.50  --bmc1_dump_file                        -
% 8.00/1.50  --bmc1_ucm_expand_uc_limit              128
% 8.00/1.50  --bmc1_ucm_n_expand_iterations          6
% 8.00/1.50  --bmc1_ucm_extend_mode                  1
% 8.00/1.50  --bmc1_ucm_init_mode                    2
% 8.00/1.50  --bmc1_ucm_cone_mode                    none
% 8.00/1.50  --bmc1_ucm_reduced_relation_type        0
% 8.00/1.50  --bmc1_ucm_relax_model                  4
% 8.00/1.50  --bmc1_ucm_full_tr_after_sat            true
% 8.00/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 8.00/1.50  --bmc1_ucm_layered_model                none
% 8.00/1.50  --bmc1_ucm_max_lemma_size               10
% 8.00/1.50  
% 8.00/1.50  ------ AIG Options
% 8.00/1.50  
% 8.00/1.50  --aig_mode                              false
% 8.00/1.50  
% 8.00/1.50  ------ Instantiation Options
% 8.00/1.50  
% 8.00/1.50  --instantiation_flag                    true
% 8.00/1.50  --inst_sos_flag                         true
% 8.00/1.50  --inst_sos_phase                        true
% 8.00/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.00/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.00/1.50  --inst_lit_sel_side                     none
% 8.00/1.50  --inst_solver_per_active                1400
% 8.00/1.50  --inst_solver_calls_frac                1.
% 8.00/1.50  --inst_passive_queue_type               priority_queues
% 8.00/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.00/1.50  --inst_passive_queues_freq              [25;2]
% 8.00/1.50  --inst_dismatching                      true
% 8.00/1.50  --inst_eager_unprocessed_to_passive     true
% 8.00/1.50  --inst_prop_sim_given                   true
% 8.00/1.50  --inst_prop_sim_new                     false
% 8.00/1.50  --inst_subs_new                         false
% 8.00/1.50  --inst_eq_res_simp                      false
% 8.00/1.50  --inst_subs_given                       false
% 8.00/1.50  --inst_orphan_elimination               true
% 8.00/1.50  --inst_learning_loop_flag               true
% 8.00/1.50  --inst_learning_start                   3000
% 8.00/1.50  --inst_learning_factor                  2
% 8.00/1.50  --inst_start_prop_sim_after_learn       3
% 8.00/1.50  --inst_sel_renew                        solver
% 8.00/1.50  --inst_lit_activity_flag                true
% 8.00/1.50  --inst_restr_to_given                   false
% 8.00/1.50  --inst_activity_threshold               500
% 8.00/1.50  --inst_out_proof                        true
% 8.00/1.50  
% 8.00/1.50  ------ Resolution Options
% 8.00/1.50  
% 8.00/1.50  --resolution_flag                       false
% 8.00/1.50  --res_lit_sel                           adaptive
% 8.00/1.50  --res_lit_sel_side                      none
% 8.00/1.50  --res_ordering                          kbo
% 8.00/1.50  --res_to_prop_solver                    active
% 8.00/1.50  --res_prop_simpl_new                    false
% 8.00/1.50  --res_prop_simpl_given                  true
% 8.00/1.50  --res_passive_queue_type                priority_queues
% 8.00/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.00/1.50  --res_passive_queues_freq               [15;5]
% 8.00/1.50  --res_forward_subs                      full
% 8.00/1.50  --res_backward_subs                     full
% 8.00/1.50  --res_forward_subs_resolution           true
% 8.00/1.50  --res_backward_subs_resolution          true
% 8.00/1.50  --res_orphan_elimination                true
% 8.00/1.50  --res_time_limit                        2.
% 8.00/1.50  --res_out_proof                         true
% 8.00/1.50  
% 8.00/1.50  ------ Superposition Options
% 8.00/1.50  
% 8.00/1.50  --superposition_flag                    true
% 8.00/1.50  --sup_passive_queue_type                priority_queues
% 8.00/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.00/1.50  --sup_passive_queues_freq               [8;1;4]
% 8.00/1.50  --demod_completeness_check              fast
% 8.00/1.50  --demod_use_ground                      true
% 8.00/1.50  --sup_to_prop_solver                    passive
% 8.00/1.50  --sup_prop_simpl_new                    true
% 8.00/1.50  --sup_prop_simpl_given                  true
% 8.00/1.50  --sup_fun_splitting                     true
% 8.00/1.50  --sup_smt_interval                      50000
% 8.00/1.50  
% 8.00/1.50  ------ Superposition Simplification Setup
% 8.00/1.50  
% 8.00/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.00/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.00/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.00/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.00/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 8.00/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.00/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.00/1.50  --sup_immed_triv                        [TrivRules]
% 8.00/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.00/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.00/1.50  --sup_immed_bw_main                     []
% 8.00/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.00/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 8.00/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.00/1.50  --sup_input_bw                          []
% 8.00/1.50  
% 8.00/1.50  ------ Combination Options
% 8.00/1.50  
% 8.00/1.50  --comb_res_mult                         3
% 8.00/1.50  --comb_sup_mult                         2
% 8.00/1.50  --comb_inst_mult                        10
% 8.00/1.50  
% 8.00/1.50  ------ Debug Options
% 8.00/1.50  
% 8.00/1.50  --dbg_backtrace                         false
% 8.00/1.50  --dbg_dump_prop_clauses                 false
% 8.00/1.50  --dbg_dump_prop_clauses_file            -
% 8.00/1.50  --dbg_out_stat                          false
% 8.00/1.50  
% 8.00/1.50  
% 8.00/1.50  
% 8.00/1.50  
% 8.00/1.50  ------ Proving...
% 8.00/1.50  
% 8.00/1.50  
% 8.00/1.50  % SZS status Theorem for theBenchmark.p
% 8.00/1.50  
% 8.00/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 8.00/1.50  
% 8.00/1.50  fof(f4,axiom,(
% 8.00/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 8.00/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f20,plain,(
% 8.00/1.50    ! [X0,X1,X2] : (m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 8.00/1.50    inference(ennf_transformation,[],[f4])).
% 8.00/1.50  
% 8.00/1.50  fof(f21,plain,(
% 8.00/1.50    ! [X0,X1,X2] : (m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 8.00/1.50    inference(flattening,[],[f20])).
% 8.00/1.50  
% 8.00/1.50  fof(f55,plain,(
% 8.00/1.50    ( ! [X2,X0,X1] : (m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f21])).
% 8.00/1.50  
% 8.00/1.50  fof(f12,conjecture,(
% 8.00/1.50    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1)))),
% 8.00/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f13,negated_conjecture,(
% 8.00/1.50    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1)))),
% 8.00/1.50    inference(negated_conjecture,[],[f12])).
% 8.00/1.50  
% 8.00/1.50  fof(f36,plain,(
% 8.00/1.50    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)))),
% 8.00/1.50    inference(ennf_transformation,[],[f13])).
% 8.00/1.50  
% 8.00/1.50  fof(f37,plain,(
% 8.00/1.50    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 8.00/1.50    inference(flattening,[],[f36])).
% 8.00/1.50  
% 8.00/1.50  fof(f50,plain,(
% 8.00/1.50    ( ! [X0,X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) => (k12_lattice3(X0,X1,k13_lattice3(X0,X1,sK4)) != X1 & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 8.00/1.50    introduced(choice_axiom,[])).
% 8.00/1.50  
% 8.00/1.50  fof(f49,plain,(
% 8.00/1.50    ( ! [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k12_lattice3(X0,sK3,k13_lattice3(X0,sK3,X2)) != sK3 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 8.00/1.50    introduced(choice_axiom,[])).
% 8.00/1.50  
% 8.00/1.50  fof(f48,plain,(
% 8.00/1.50    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => (? [X1] : (? [X2] : (k12_lattice3(sK2,X1,k13_lattice3(sK2,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_orders_2(sK2) & v2_lattice3(sK2) & v1_lattice3(sK2) & v5_orders_2(sK2) & v3_orders_2(sK2))),
% 8.00/1.50    introduced(choice_axiom,[])).
% 8.00/1.50  
% 8.00/1.50  fof(f51,plain,(
% 8.00/1.50    ((k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 & m1_subset_1(sK4,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_orders_2(sK2) & v2_lattice3(sK2) & v1_lattice3(sK2) & v5_orders_2(sK2) & v3_orders_2(sK2)),
% 8.00/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f37,f50,f49,f48])).
% 8.00/1.50  
% 8.00/1.50  fof(f79,plain,(
% 8.00/1.50    l1_orders_2(sK2)),
% 8.00/1.50    inference(cnf_transformation,[],[f51])).
% 8.00/1.50  
% 8.00/1.50  fof(f6,axiom,(
% 8.00/1.50    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 8.00/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f24,plain,(
% 8.00/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 8.00/1.50    inference(ennf_transformation,[],[f6])).
% 8.00/1.50  
% 8.00/1.50  fof(f25,plain,(
% 8.00/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 8.00/1.50    inference(flattening,[],[f24])).
% 8.00/1.50  
% 8.00/1.50  fof(f38,plain,(
% 8.00/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3))) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 8.00/1.50    inference(nnf_transformation,[],[f25])).
% 8.00/1.50  
% 8.00/1.50  fof(f39,plain,(
% 8.00/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 8.00/1.50    inference(flattening,[],[f38])).
% 8.00/1.50  
% 8.00/1.50  fof(f40,plain,(
% 8.00/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 8.00/1.50    inference(rectify,[],[f39])).
% 8.00/1.50  
% 8.00/1.50  fof(f41,plain,(
% 8.00/1.50    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,X3,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))))),
% 8.00/1.50    introduced(choice_axiom,[])).
% 8.00/1.50  
% 8.00/1.50  fof(f42,plain,(
% 8.00/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,X3,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 8.00/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).
% 8.00/1.50  
% 8.00/1.50  fof(f57,plain,(
% 8.00/1.50    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X1,X3) | k10_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f42])).
% 8.00/1.50  
% 8.00/1.50  fof(f85,plain,(
% 8.00/1.50    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 8.00/1.50    inference(equality_resolution,[],[f57])).
% 8.00/1.50  
% 8.00/1.50  fof(f2,axiom,(
% 8.00/1.50    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 8.00/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f16,plain,(
% 8.00/1.50    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 8.00/1.50    inference(ennf_transformation,[],[f2])).
% 8.00/1.50  
% 8.00/1.50  fof(f17,plain,(
% 8.00/1.50    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 8.00/1.50    inference(flattening,[],[f16])).
% 8.00/1.50  
% 8.00/1.50  fof(f53,plain,(
% 8.00/1.50    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f17])).
% 8.00/1.50  
% 8.00/1.50  fof(f77,plain,(
% 8.00/1.50    v1_lattice3(sK2)),
% 8.00/1.50    inference(cnf_transformation,[],[f51])).
% 8.00/1.50  
% 8.00/1.50  fof(f76,plain,(
% 8.00/1.50    v5_orders_2(sK2)),
% 8.00/1.50    inference(cnf_transformation,[],[f51])).
% 8.00/1.50  
% 8.00/1.50  fof(f80,plain,(
% 8.00/1.50    m1_subset_1(sK3,u1_struct_0(sK2))),
% 8.00/1.50    inference(cnf_transformation,[],[f51])).
% 8.00/1.50  
% 8.00/1.50  fof(f5,axiom,(
% 8.00/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 8.00/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f22,plain,(
% 8.00/1.50    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 8.00/1.50    inference(ennf_transformation,[],[f5])).
% 8.00/1.50  
% 8.00/1.50  fof(f23,plain,(
% 8.00/1.50    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 8.00/1.50    inference(flattening,[],[f22])).
% 8.00/1.50  
% 8.00/1.50  fof(f56,plain,(
% 8.00/1.50    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f23])).
% 8.00/1.50  
% 8.00/1.50  fof(f9,axiom,(
% 8.00/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2))),
% 8.00/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f30,plain,(
% 8.00/1.50    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 8.00/1.50    inference(ennf_transformation,[],[f9])).
% 8.00/1.50  
% 8.00/1.50  fof(f31,plain,(
% 8.00/1.50    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 8.00/1.50    inference(flattening,[],[f30])).
% 8.00/1.50  
% 8.00/1.50  fof(f72,plain,(
% 8.00/1.50    ( ! [X2,X0,X1] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f31])).
% 8.00/1.50  
% 8.00/1.50  fof(f8,axiom,(
% 8.00/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2))),
% 8.00/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f28,plain,(
% 8.00/1.50    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 8.00/1.50    inference(ennf_transformation,[],[f8])).
% 8.00/1.50  
% 8.00/1.50  fof(f29,plain,(
% 8.00/1.50    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 8.00/1.50    inference(flattening,[],[f28])).
% 8.00/1.50  
% 8.00/1.50  fof(f71,plain,(
% 8.00/1.50    ( ! [X2,X0,X1] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f29])).
% 8.00/1.50  
% 8.00/1.50  fof(f78,plain,(
% 8.00/1.50    v2_lattice3(sK2)),
% 8.00/1.50    inference(cnf_transformation,[],[f51])).
% 8.00/1.50  
% 8.00/1.50  fof(f11,axiom,(
% 8.00/1.50    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2)))),
% 8.00/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f34,plain,(
% 8.00/1.50    ! [X0] : (! [X1] : (! [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)))),
% 8.00/1.50    inference(ennf_transformation,[],[f11])).
% 8.00/1.50  
% 8.00/1.50  fof(f35,plain,(
% 8.00/1.50    ! [X0] : (! [X1] : (! [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 8.00/1.50    inference(flattening,[],[f34])).
% 8.00/1.50  
% 8.00/1.50  fof(f74,plain,(
% 8.00/1.50    ( ! [X2,X0,X1] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f35])).
% 8.00/1.50  
% 8.00/1.50  fof(f75,plain,(
% 8.00/1.50    v3_orders_2(sK2)),
% 8.00/1.50    inference(cnf_transformation,[],[f51])).
% 8.00/1.50  
% 8.00/1.50  fof(f58,plain,(
% 8.00/1.50    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X2,X3) | k10_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f42])).
% 8.00/1.50  
% 8.00/1.50  fof(f84,plain,(
% 8.00/1.50    ( ! [X2,X0,X1] : (r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 8.00/1.50    inference(equality_resolution,[],[f58])).
% 8.00/1.50  
% 8.00/1.50  fof(f7,axiom,(
% 8.00/1.50    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 8.00/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f26,plain,(
% 8.00/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 8.00/1.50    inference(ennf_transformation,[],[f7])).
% 8.00/1.50  
% 8.00/1.50  fof(f27,plain,(
% 8.00/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 8.00/1.50    inference(flattening,[],[f26])).
% 8.00/1.50  
% 8.00/1.50  fof(f43,plain,(
% 8.00/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 8.00/1.50    inference(nnf_transformation,[],[f27])).
% 8.00/1.50  
% 8.00/1.50  fof(f44,plain,(
% 8.00/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 8.00/1.50    inference(flattening,[],[f43])).
% 8.00/1.50  
% 8.00/1.50  fof(f45,plain,(
% 8.00/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 8.00/1.50    inference(rectify,[],[f44])).
% 8.00/1.50  
% 8.00/1.50  fof(f46,plain,(
% 8.00/1.50    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK1(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X1) & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0))))),
% 8.00/1.50    introduced(choice_axiom,[])).
% 8.00/1.50  
% 8.00/1.50  fof(f47,plain,(
% 8.00/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,sK1(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X1) & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 8.00/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f45,f46])).
% 8.00/1.50  
% 8.00/1.50  fof(f66,plain,(
% 8.00/1.50    ( ! [X2,X0,X5,X3,X1] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | k11_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f47])).
% 8.00/1.50  
% 8.00/1.50  fof(f86,plain,(
% 8.00/1.50    ( ! [X2,X0,X5,X1] : (r1_orders_2(X0,X5,k11_lattice3(X0,X1,X2)) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 8.00/1.50    inference(equality_resolution,[],[f66])).
% 8.00/1.50  
% 8.00/1.50  fof(f3,axiom,(
% 8.00/1.50    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 8.00/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f18,plain,(
% 8.00/1.50    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 8.00/1.50    inference(ennf_transformation,[],[f3])).
% 8.00/1.50  
% 8.00/1.50  fof(f19,plain,(
% 8.00/1.50    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 8.00/1.50    inference(flattening,[],[f18])).
% 8.00/1.50  
% 8.00/1.50  fof(f54,plain,(
% 8.00/1.50    ( ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f19])).
% 8.00/1.50  
% 8.00/1.50  fof(f1,axiom,(
% 8.00/1.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2)) => X1 = X2))))),
% 8.00/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f14,plain,(
% 8.00/1.50    ! [X0] : (! [X1] : (! [X2] : ((X1 = X2 | (~r1_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 8.00/1.50    inference(ennf_transformation,[],[f1])).
% 8.00/1.50  
% 8.00/1.50  fof(f15,plain,(
% 8.00/1.50    ! [X0] : (! [X1] : (! [X2] : (X1 = X2 | ~r1_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 8.00/1.50    inference(flattening,[],[f14])).
% 8.00/1.50  
% 8.00/1.50  fof(f52,plain,(
% 8.00/1.50    ( ! [X2,X0,X1] : (X1 = X2 | ~r1_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f15])).
% 8.00/1.50  
% 8.00/1.50  fof(f81,plain,(
% 8.00/1.50    m1_subset_1(sK4,u1_struct_0(sK2))),
% 8.00/1.50    inference(cnf_transformation,[],[f51])).
% 8.00/1.50  
% 8.00/1.50  fof(f64,plain,(
% 8.00/1.50    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X3,X1) | k11_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f47])).
% 8.00/1.50  
% 8.00/1.50  fof(f88,plain,(
% 8.00/1.50    ( ! [X2,X0,X1] : (r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1) | ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 8.00/1.50    inference(equality_resolution,[],[f64])).
% 8.00/1.50  
% 8.00/1.50  fof(f82,plain,(
% 8.00/1.50    k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3),
% 8.00/1.50    inference(cnf_transformation,[],[f51])).
% 8.00/1.50  
% 8.00/1.50  cnf(c_3,plain,
% 8.00/1.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 8.00/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 8.00/1.50      | m1_subset_1(k10_lattice3(X1,X2,X0),u1_struct_0(X1))
% 8.00/1.50      | ~ l1_orders_2(X1) ),
% 8.00/1.50      inference(cnf_transformation,[],[f55]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_26,negated_conjecture,
% 8.00/1.50      ( l1_orders_2(sK2) ),
% 8.00/1.50      inference(cnf_transformation,[],[f79]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1054,plain,
% 8.00/1.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 8.00/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 8.00/1.50      | m1_subset_1(k10_lattice3(X1,X2,X0),u1_struct_0(X1))
% 8.00/1.50      | sK2 != X1 ),
% 8.00/1.50      inference(resolution_lifted,[status(thm)],[c_3,c_26]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1055,plain,
% 8.00/1.50      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 8.00/1.50      | m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
% 8.00/1.50      inference(unflattening,[status(thm)],[c_1054]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_11,plain,
% 8.00/1.50      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 8.00/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 8.00/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 8.00/1.50      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 8.00/1.50      | ~ v1_lattice3(X0)
% 8.00/1.50      | v2_struct_0(X0)
% 8.00/1.50      | ~ v5_orders_2(X0)
% 8.00/1.50      | ~ l1_orders_2(X0) ),
% 8.00/1.50      inference(cnf_transformation,[],[f85]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1,plain,
% 8.00/1.50      ( ~ v1_lattice3(X0) | ~ v2_struct_0(X0) | ~ l1_orders_2(X0) ),
% 8.00/1.50      inference(cnf_transformation,[],[f53]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_216,plain,
% 8.00/1.50      ( ~ v1_lattice3(X0)
% 8.00/1.50      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 8.00/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 8.00/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 8.00/1.50      | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 8.00/1.50      | ~ v5_orders_2(X0)
% 8.00/1.50      | ~ l1_orders_2(X0) ),
% 8.00/1.50      inference(global_propositional_subsumption,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_11,c_1]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_217,plain,
% 8.00/1.50      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 8.00/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 8.00/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 8.00/1.50      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 8.00/1.50      | ~ v1_lattice3(X0)
% 8.00/1.50      | ~ v5_orders_2(X0)
% 8.00/1.50      | ~ l1_orders_2(X0) ),
% 8.00/1.50      inference(renaming,[status(thm)],[c_216]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_28,negated_conjecture,
% 8.00/1.50      ( v1_lattice3(sK2) ),
% 8.00/1.50      inference(cnf_transformation,[],[f77]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_606,plain,
% 8.00/1.50      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 8.00/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 8.00/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 8.00/1.50      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 8.00/1.50      | ~ v5_orders_2(X0)
% 8.00/1.50      | ~ l1_orders_2(X0)
% 8.00/1.50      | sK2 != X0 ),
% 8.00/1.50      inference(resolution_lifted,[status(thm)],[c_217,c_28]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_607,plain,
% 8.00/1.50      ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
% 8.00/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2))
% 8.00/1.50      | ~ v5_orders_2(sK2)
% 8.00/1.50      | ~ l1_orders_2(sK2) ),
% 8.00/1.50      inference(unflattening,[status(thm)],[c_606]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_29,negated_conjecture,
% 8.00/1.50      ( v5_orders_2(sK2) ),
% 8.00/1.50      inference(cnf_transformation,[],[f76]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_609,plain,
% 8.00/1.50      ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
% 8.00/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
% 8.00/1.50      inference(global_propositional_subsumption,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_607,c_29,c_26]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_610,plain,
% 8.00/1.50      ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
% 8.00/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
% 8.00/1.50      inference(renaming,[status(thm)],[c_609]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1087,plain,
% 8.00/1.50      ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
% 8.00/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 8.00/1.50      inference(backward_subsumption_resolution,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_1055,c_610]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1248,plain,
% 8.00/1.50      ( r1_orders_2(sK2,X0_47,k10_lattice3(sK2,X0_47,X1_47))
% 8.00/1.50      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(X1_47,u1_struct_0(sK2)) ),
% 8.00/1.50      inference(subtyping,[status(esa)],[c_1087]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_24920,plain,
% 8.00/1.50      ( r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK4))
% 8.00/1.50      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_1248]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_25,negated_conjecture,
% 8.00/1.50      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 8.00/1.50      inference(cnf_transformation,[],[f80]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1268,negated_conjecture,
% 8.00/1.50      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 8.00/1.50      inference(subtyping,[status(esa)],[c_25]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1663,plain,
% 8.00/1.50      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_1268]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_4,plain,
% 8.00/1.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 8.00/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 8.00/1.50      | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
% 8.00/1.50      | ~ l1_orders_2(X1) ),
% 8.00/1.50      inference(cnf_transformation,[],[f56]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1039,plain,
% 8.00/1.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 8.00/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 8.00/1.50      | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
% 8.00/1.50      | sK2 != X1 ),
% 8.00/1.50      inference(resolution_lifted,[status(thm)],[c_4,c_26]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1040,plain,
% 8.00/1.50      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 8.00/1.50      | m1_subset_1(k11_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
% 8.00/1.50      inference(unflattening,[status(thm)],[c_1039]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1254,plain,
% 8.00/1.50      ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 8.00/1.50      | m1_subset_1(k11_lattice3(sK2,X0_47,X1_47),u1_struct_0(sK2)) ),
% 8.00/1.50      inference(subtyping,[status(esa)],[c_1040]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1677,plain,
% 8.00/1.50      ( m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 8.00/1.50      | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top
% 8.00/1.50      | m1_subset_1(k11_lattice3(sK2,X0_47,X1_47),u1_struct_0(sK2)) = iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_1254]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_20,plain,
% 8.00/1.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 8.00/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 8.00/1.50      | ~ v1_lattice3(X1)
% 8.00/1.50      | ~ v5_orders_2(X1)
% 8.00/1.50      | ~ l1_orders_2(X1)
% 8.00/1.50      | k13_lattice3(X1,X2,X0) = k10_lattice3(X1,X2,X0) ),
% 8.00/1.50      inference(cnf_transformation,[],[f72]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_626,plain,
% 8.00/1.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 8.00/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 8.00/1.50      | ~ v5_orders_2(X1)
% 8.00/1.50      | ~ l1_orders_2(X1)
% 8.00/1.50      | k13_lattice3(X1,X2,X0) = k10_lattice3(X1,X2,X0)
% 8.00/1.50      | sK2 != X1 ),
% 8.00/1.50      inference(resolution_lifted,[status(thm)],[c_20,c_28]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_627,plain,
% 8.00/1.50      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 8.00/1.50      | ~ v5_orders_2(sK2)
% 8.00/1.50      | ~ l1_orders_2(sK2)
% 8.00/1.50      | k13_lattice3(sK2,X0,X1) = k10_lattice3(sK2,X0,X1) ),
% 8.00/1.50      inference(unflattening,[status(thm)],[c_626]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_631,plain,
% 8.00/1.50      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 8.00/1.50      | k13_lattice3(sK2,X0,X1) = k10_lattice3(sK2,X0,X1) ),
% 8.00/1.50      inference(global_propositional_subsumption,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_627,c_29,c_26]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1262,plain,
% 8.00/1.50      ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 8.00/1.50      | k13_lattice3(sK2,X0_47,X1_47) = k10_lattice3(sK2,X0_47,X1_47) ),
% 8.00/1.50      inference(subtyping,[status(esa)],[c_631]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1669,plain,
% 8.00/1.50      ( k13_lattice3(sK2,X0_47,X1_47) = k10_lattice3(sK2,X0_47,X1_47)
% 8.00/1.50      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 8.00/1.50      | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_1262]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2447,plain,
% 8.00/1.50      ( k13_lattice3(sK2,k11_lattice3(sK2,X0_47,X1_47),X2_47) = k10_lattice3(sK2,k11_lattice3(sK2,X0_47,X1_47),X2_47)
% 8.00/1.50      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 8.00/1.50      | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top
% 8.00/1.50      | m1_subset_1(X2_47,u1_struct_0(sK2)) != iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_1677,c_1669]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_17026,plain,
% 8.00/1.50      ( k13_lattice3(sK2,k11_lattice3(sK2,sK3,X0_47),X1_47) = k10_lattice3(sK2,k11_lattice3(sK2,sK3,X0_47),X1_47)
% 8.00/1.50      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 8.00/1.50      | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_1663,c_2447]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_18096,plain,
% 8.00/1.50      ( k13_lattice3(sK2,k11_lattice3(sK2,sK3,sK3),X0_47) = k10_lattice3(sK2,k11_lattice3(sK2,sK3,sK3),X0_47)
% 8.00/1.50      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_1663,c_17026]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_18282,plain,
% 8.00/1.50      ( k13_lattice3(sK2,k11_lattice3(sK2,sK3,sK3),sK3) = k10_lattice3(sK2,k11_lattice3(sK2,sK3,sK3),sK3) ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_1663,c_18096]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_19,plain,
% 8.00/1.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 8.00/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 8.00/1.50      | ~ v2_lattice3(X1)
% 8.00/1.50      | ~ v5_orders_2(X1)
% 8.00/1.50      | ~ l1_orders_2(X1)
% 8.00/1.50      | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0) ),
% 8.00/1.50      inference(cnf_transformation,[],[f71]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_27,negated_conjecture,
% 8.00/1.50      ( v2_lattice3(sK2) ),
% 8.00/1.50      inference(cnf_transformation,[],[f78]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_927,plain,
% 8.00/1.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 8.00/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 8.00/1.50      | ~ v5_orders_2(X1)
% 8.00/1.50      | ~ l1_orders_2(X1)
% 8.00/1.50      | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0)
% 8.00/1.50      | sK2 != X1 ),
% 8.00/1.50      inference(resolution_lifted,[status(thm)],[c_19,c_27]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_928,plain,
% 8.00/1.50      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 8.00/1.50      | ~ v5_orders_2(sK2)
% 8.00/1.50      | ~ l1_orders_2(sK2)
% 8.00/1.50      | k12_lattice3(sK2,X0,X1) = k11_lattice3(sK2,X0,X1) ),
% 8.00/1.50      inference(unflattening,[status(thm)],[c_927]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_932,plain,
% 8.00/1.50      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 8.00/1.50      | k12_lattice3(sK2,X0,X1) = k11_lattice3(sK2,X0,X1) ),
% 8.00/1.50      inference(global_propositional_subsumption,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_928,c_29,c_26]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1256,plain,
% 8.00/1.50      ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 8.00/1.50      | k12_lattice3(sK2,X0_47,X1_47) = k11_lattice3(sK2,X0_47,X1_47) ),
% 8.00/1.50      inference(subtyping,[status(esa)],[c_932]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1675,plain,
% 8.00/1.50      ( k12_lattice3(sK2,X0_47,X1_47) = k11_lattice3(sK2,X0_47,X1_47)
% 8.00/1.50      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 8.00/1.50      | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_1256]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_5504,plain,
% 8.00/1.50      ( k12_lattice3(sK2,sK3,X0_47) = k11_lattice3(sK2,sK3,X0_47)
% 8.00/1.50      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_1663,c_1675]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_5604,plain,
% 8.00/1.50      ( k12_lattice3(sK2,sK3,sK3) = k11_lattice3(sK2,sK3,sK3) ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_1663,c_5504]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_22,plain,
% 8.00/1.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 8.00/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 8.00/1.50      | ~ v3_orders_2(X1)
% 8.00/1.50      | ~ v2_lattice3(X1)
% 8.00/1.50      | ~ v1_lattice3(X1)
% 8.00/1.50      | ~ v5_orders_2(X1)
% 8.00/1.50      | ~ l1_orders_2(X1)
% 8.00/1.50      | k13_lattice3(X1,k12_lattice3(X1,X2,X0),X0) = X0 ),
% 8.00/1.50      inference(cnf_transformation,[],[f74]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_30,negated_conjecture,
% 8.00/1.50      ( v3_orders_2(sK2) ),
% 8.00/1.50      inference(cnf_transformation,[],[f75]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_396,plain,
% 8.00/1.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 8.00/1.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 8.00/1.50      | ~ v2_lattice3(X1)
% 8.00/1.50      | ~ v1_lattice3(X1)
% 8.00/1.50      | ~ v5_orders_2(X1)
% 8.00/1.50      | ~ l1_orders_2(X1)
% 8.00/1.50      | k13_lattice3(X1,k12_lattice3(X1,X2,X0),X0) = X0
% 8.00/1.50      | sK2 != X1 ),
% 8.00/1.50      inference(resolution_lifted,[status(thm)],[c_22,c_30]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_397,plain,
% 8.00/1.50      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 8.00/1.50      | ~ v2_lattice3(sK2)
% 8.00/1.50      | ~ v1_lattice3(sK2)
% 8.00/1.50      | ~ v5_orders_2(sK2)
% 8.00/1.50      | ~ l1_orders_2(sK2)
% 8.00/1.50      | k13_lattice3(sK2,k12_lattice3(sK2,X0,X1),X1) = X1 ),
% 8.00/1.50      inference(unflattening,[status(thm)],[c_396]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_401,plain,
% 8.00/1.50      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 8.00/1.50      | k13_lattice3(sK2,k12_lattice3(sK2,X0,X1),X1) = X1 ),
% 8.00/1.50      inference(global_propositional_subsumption,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_397,c_29,c_28,c_27,c_26]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1267,plain,
% 8.00/1.50      ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 8.00/1.50      | k13_lattice3(sK2,k12_lattice3(sK2,X0_47,X1_47),X1_47) = X1_47 ),
% 8.00/1.50      inference(subtyping,[status(esa)],[c_401]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1664,plain,
% 8.00/1.50      ( k13_lattice3(sK2,k12_lattice3(sK2,X0_47,X1_47),X1_47) = X1_47
% 8.00/1.50      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 8.00/1.50      | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_1267]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1811,plain,
% 8.00/1.50      ( k13_lattice3(sK2,k12_lattice3(sK2,sK3,X0_47),X0_47) = X0_47
% 8.00/1.50      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_1663,c_1664]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2152,plain,
% 8.00/1.50      ( k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK3),sK3) = sK3 ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_1663,c_1811]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_5683,plain,
% 8.00/1.50      ( k13_lattice3(sK2,k11_lattice3(sK2,sK3,sK3),sK3) = sK3 ),
% 8.00/1.50      inference(demodulation,[status(thm)],[c_5604,c_2152]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_18287,plain,
% 8.00/1.50      ( k10_lattice3(sK2,k11_lattice3(sK2,sK3,sK3),sK3) = sK3 ),
% 8.00/1.50      inference(light_normalisation,[status(thm)],[c_18282,c_5683]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_10,plain,
% 8.00/1.50      ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
% 8.00/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 8.00/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 8.00/1.50      | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
% 8.00/1.50      | ~ v1_lattice3(X0)
% 8.00/1.50      | v2_struct_0(X0)
% 8.00/1.50      | ~ v5_orders_2(X0)
% 8.00/1.50      | ~ l1_orders_2(X0) ),
% 8.00/1.50      inference(cnf_transformation,[],[f84]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_223,plain,
% 8.00/1.50      ( ~ v1_lattice3(X0)
% 8.00/1.50      | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
% 8.00/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 8.00/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 8.00/1.50      | r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
% 8.00/1.50      | ~ v5_orders_2(X0)
% 8.00/1.50      | ~ l1_orders_2(X0) ),
% 8.00/1.50      inference(global_propositional_subsumption,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_10,c_1]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_224,plain,
% 8.00/1.50      ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
% 8.00/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 8.00/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 8.00/1.50      | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
% 8.00/1.50      | ~ v1_lattice3(X0)
% 8.00/1.50      | ~ v5_orders_2(X0)
% 8.00/1.50      | ~ l1_orders_2(X0) ),
% 8.00/1.50      inference(renaming,[status(thm)],[c_223]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_582,plain,
% 8.00/1.50      ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
% 8.00/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 8.00/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 8.00/1.50      | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
% 8.00/1.50      | ~ v5_orders_2(X0)
% 8.00/1.50      | ~ l1_orders_2(X0)
% 8.00/1.50      | sK2 != X0 ),
% 8.00/1.50      inference(resolution_lifted,[status(thm)],[c_224,c_28]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_583,plain,
% 8.00/1.50      ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X1,X0))
% 8.00/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(k10_lattice3(sK2,X1,X0),u1_struct_0(sK2))
% 8.00/1.50      | ~ v5_orders_2(sK2)
% 8.00/1.50      | ~ l1_orders_2(sK2) ),
% 8.00/1.50      inference(unflattening,[status(thm)],[c_582]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_587,plain,
% 8.00/1.50      ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X1,X0))
% 8.00/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(k10_lattice3(sK2,X1,X0),u1_struct_0(sK2)) ),
% 8.00/1.50      inference(global_propositional_subsumption,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_583,c_29,c_26]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_588,plain,
% 8.00/1.50      ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X1,X0))
% 8.00/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(k10_lattice3(sK2,X1,X0),u1_struct_0(sK2)) ),
% 8.00/1.50      inference(renaming,[status(thm)],[c_587]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1088,plain,
% 8.00/1.50      ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X1,X0))
% 8.00/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 8.00/1.50      inference(backward_subsumption_resolution,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_1055,c_588]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1247,plain,
% 8.00/1.50      ( r1_orders_2(sK2,X0_47,k10_lattice3(sK2,X1_47,X0_47))
% 8.00/1.50      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(X1_47,u1_struct_0(sK2)) ),
% 8.00/1.50      inference(subtyping,[status(esa)],[c_1088]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1684,plain,
% 8.00/1.50      ( r1_orders_2(sK2,X0_47,k10_lattice3(sK2,X1_47,X0_47)) = iProver_top
% 8.00/1.50      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 8.00/1.50      | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_1247]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_18528,plain,
% 8.00/1.50      ( r1_orders_2(sK2,sK3,sK3) = iProver_top
% 8.00/1.50      | m1_subset_1(k11_lattice3(sK2,sK3,sK3),u1_struct_0(sK2)) != iProver_top
% 8.00/1.50      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_18287,c_1684]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1274,plain,
% 8.00/1.50      ( ~ r1_orders_2(X0_46,X0_47,X1_47)
% 8.00/1.50      | r1_orders_2(X0_46,X2_47,X3_47)
% 8.00/1.50      | X2_47 != X0_47
% 8.00/1.50      | X3_47 != X1_47 ),
% 8.00/1.50      theory(equality) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1736,plain,
% 8.00/1.50      ( ~ r1_orders_2(sK2,X0_47,X1_47)
% 8.00/1.50      | r1_orders_2(sK2,X2_47,X3_47)
% 8.00/1.50      | X2_47 != X0_47
% 8.00/1.50      | X3_47 != X1_47 ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_1274]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1915,plain,
% 8.00/1.50      ( r1_orders_2(sK2,X0_47,X1_47)
% 8.00/1.50      | ~ r1_orders_2(sK2,X2_47,k10_lattice3(sK2,X2_47,X3_47))
% 8.00/1.50      | X0_47 != X2_47
% 8.00/1.50      | X1_47 != k10_lattice3(sK2,X2_47,X3_47) ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_1736]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2379,plain,
% 8.00/1.50      ( r1_orders_2(sK2,X0_47,k13_lattice3(sK2,X1_47,X2_47))
% 8.00/1.50      | ~ r1_orders_2(sK2,X1_47,k10_lattice3(sK2,X1_47,X2_47))
% 8.00/1.50      | X0_47 != X1_47
% 8.00/1.50      | k13_lattice3(sK2,X1_47,X2_47) != k10_lattice3(sK2,X1_47,X2_47) ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_1915]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_7439,plain,
% 8.00/1.50      ( r1_orders_2(sK2,X0_47,k13_lattice3(sK2,sK3,sK4))
% 8.00/1.50      | ~ r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK4))
% 8.00/1.50      | X0_47 != sK3
% 8.00/1.50      | k13_lattice3(sK2,sK3,sK4) != k10_lattice3(sK2,sK3,sK4) ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_2379]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_7446,plain,
% 8.00/1.50      ( r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
% 8.00/1.50      | ~ r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK4))
% 8.00/1.50      | k13_lattice3(sK2,sK3,sK4) != k10_lattice3(sK2,sK3,sK4)
% 8.00/1.50      | sK3 != sK3 ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_7439]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_16,plain,
% 8.00/1.50      ( ~ r1_orders_2(X0,X1,X2)
% 8.00/1.50      | ~ r1_orders_2(X0,X1,X3)
% 8.00/1.50      | r1_orders_2(X0,X1,k11_lattice3(X0,X3,X2))
% 8.00/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 8.00/1.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 8.00/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 8.00/1.50      | ~ m1_subset_1(k11_lattice3(X0,X3,X2),u1_struct_0(X0))
% 8.00/1.50      | ~ v2_lattice3(X0)
% 8.00/1.50      | v2_struct_0(X0)
% 8.00/1.50      | ~ v5_orders_2(X0)
% 8.00/1.50      | ~ l1_orders_2(X0) ),
% 8.00/1.50      inference(cnf_transformation,[],[f86]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2,plain,
% 8.00/1.50      ( ~ v2_lattice3(X0) | ~ v2_struct_0(X0) | ~ l1_orders_2(X0) ),
% 8.00/1.50      inference(cnf_transformation,[],[f54]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_183,plain,
% 8.00/1.50      ( ~ v2_lattice3(X0)
% 8.00/1.50      | ~ m1_subset_1(k11_lattice3(X0,X3,X2),u1_struct_0(X0))
% 8.00/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 8.00/1.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 8.00/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 8.00/1.50      | r1_orders_2(X0,X1,k11_lattice3(X0,X3,X2))
% 8.00/1.50      | ~ r1_orders_2(X0,X1,X3)
% 8.00/1.50      | ~ r1_orders_2(X0,X1,X2)
% 8.00/1.50      | ~ v5_orders_2(X0)
% 8.00/1.50      | ~ l1_orders_2(X0) ),
% 8.00/1.50      inference(global_propositional_subsumption,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_16,c_2]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_184,plain,
% 8.00/1.50      ( ~ r1_orders_2(X0,X1,X2)
% 8.00/1.50      | ~ r1_orders_2(X0,X1,X3)
% 8.00/1.50      | r1_orders_2(X0,X1,k11_lattice3(X0,X3,X2))
% 8.00/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 8.00/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 8.00/1.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 8.00/1.50      | ~ m1_subset_1(k11_lattice3(X0,X3,X2),u1_struct_0(X0))
% 8.00/1.50      | ~ v2_lattice3(X0)
% 8.00/1.50      | ~ v5_orders_2(X0)
% 8.00/1.50      | ~ l1_orders_2(X0) ),
% 8.00/1.50      inference(renaming,[status(thm)],[c_183]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_829,plain,
% 8.00/1.50      ( ~ r1_orders_2(X0,X1,X2)
% 8.00/1.50      | ~ r1_orders_2(X0,X1,X3)
% 8.00/1.50      | r1_orders_2(X0,X1,k11_lattice3(X0,X3,X2))
% 8.00/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 8.00/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 8.00/1.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 8.00/1.50      | ~ m1_subset_1(k11_lattice3(X0,X3,X2),u1_struct_0(X0))
% 8.00/1.50      | ~ v5_orders_2(X0)
% 8.00/1.50      | ~ l1_orders_2(X0)
% 8.00/1.50      | sK2 != X0 ),
% 8.00/1.50      inference(resolution_lifted,[status(thm)],[c_184,c_27]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_830,plain,
% 8.00/1.50      ( ~ r1_orders_2(sK2,X0,X1)
% 8.00/1.50      | ~ r1_orders_2(sK2,X0,X2)
% 8.00/1.50      | r1_orders_2(sK2,X0,k11_lattice3(sK2,X2,X1))
% 8.00/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(k11_lattice3(sK2,X2,X1),u1_struct_0(sK2))
% 8.00/1.50      | ~ v5_orders_2(sK2)
% 8.00/1.50      | ~ l1_orders_2(sK2) ),
% 8.00/1.50      inference(unflattening,[status(thm)],[c_829]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_834,plain,
% 8.00/1.50      ( ~ r1_orders_2(sK2,X0,X1)
% 8.00/1.50      | ~ r1_orders_2(sK2,X0,X2)
% 8.00/1.50      | r1_orders_2(sK2,X0,k11_lattice3(sK2,X2,X1))
% 8.00/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(k11_lattice3(sK2,X2,X1),u1_struct_0(sK2)) ),
% 8.00/1.50      inference(global_propositional_subsumption,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_830,c_29,c_26]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_835,plain,
% 8.00/1.50      ( ~ r1_orders_2(sK2,X0,X1)
% 8.00/1.50      | ~ r1_orders_2(sK2,X0,X2)
% 8.00/1.50      | r1_orders_2(sK2,X0,k11_lattice3(sK2,X2,X1))
% 8.00/1.50      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(k11_lattice3(sK2,X2,X1),u1_struct_0(sK2)) ),
% 8.00/1.50      inference(renaming,[status(thm)],[c_834]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1072,plain,
% 8.00/1.50      ( ~ r1_orders_2(sK2,X0,X1)
% 8.00/1.50      | ~ r1_orders_2(sK2,X0,X2)
% 8.00/1.50      | r1_orders_2(sK2,X0,k11_lattice3(sK2,X2,X1))
% 8.00/1.50      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 8.00/1.50      inference(backward_subsumption_resolution,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_1040,c_835]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1252,plain,
% 8.00/1.50      ( ~ r1_orders_2(sK2,X0_47,X1_47)
% 8.00/1.50      | ~ r1_orders_2(sK2,X0_47,X2_47)
% 8.00/1.50      | r1_orders_2(sK2,X0_47,k11_lattice3(sK2,X2_47,X1_47))
% 8.00/1.50      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(X2_47,u1_struct_0(sK2)) ),
% 8.00/1.50      inference(subtyping,[status(esa)],[c_1072]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2852,plain,
% 8.00/1.50      ( ~ r1_orders_2(sK2,X0_47,X1_47)
% 8.00/1.50      | ~ r1_orders_2(sK2,X0_47,k13_lattice3(sK2,X2_47,X3_47))
% 8.00/1.50      | r1_orders_2(sK2,X0_47,k11_lattice3(sK2,X1_47,k13_lattice3(sK2,X2_47,X3_47)))
% 8.00/1.50      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(k13_lattice3(sK2,X2_47,X3_47),u1_struct_0(sK2)) ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_1252]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_7117,plain,
% 8.00/1.50      ( ~ r1_orders_2(sK2,X0_47,X1_47)
% 8.00/1.50      | ~ r1_orders_2(sK2,X0_47,k13_lattice3(sK2,sK3,sK4))
% 8.00/1.50      | r1_orders_2(sK2,X0_47,k11_lattice3(sK2,X1_47,k13_lattice3(sK2,sK3,sK4)))
% 8.00/1.50      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_2852]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_7147,plain,
% 8.00/1.50      ( ~ r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
% 8.00/1.50      | r1_orders_2(sK2,sK3,k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)))
% 8.00/1.50      | ~ r1_orders_2(sK2,sK3,sK3)
% 8.00/1.50      | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_7117]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_4306,plain,
% 8.00/1.50      ( ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 8.00/1.50      | m1_subset_1(k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)),u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_1254]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1253,plain,
% 8.00/1.50      ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 8.00/1.50      | m1_subset_1(k10_lattice3(sK2,X0_47,X1_47),u1_struct_0(sK2)) ),
% 8.00/1.50      inference(subtyping,[status(esa)],[c_1055]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_4295,plain,
% 8.00/1.50      ( m1_subset_1(k10_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_1253]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1275,plain,
% 8.00/1.50      ( ~ m1_subset_1(X0_47,X0_48)
% 8.00/1.50      | m1_subset_1(X1_47,X0_48)
% 8.00/1.50      | X1_47 != X0_47 ),
% 8.00/1.50      theory(equality) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2132,plain,
% 8.00/1.50      ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 8.00/1.50      | m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 8.00/1.50      | k13_lattice3(sK2,sK3,sK4) != X0_47 ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_1275]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_3685,plain,
% 8.00/1.50      ( m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(k10_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 8.00/1.50      | k13_lattice3(sK2,sK3,sK4) != k10_lattice3(sK2,sK3,sK4) ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_2132]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_0,plain,
% 8.00/1.50      ( ~ r1_orders_2(X0,X1,X2)
% 8.00/1.50      | ~ r1_orders_2(X0,X2,X1)
% 8.00/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 8.00/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 8.00/1.50      | ~ v5_orders_2(X0)
% 8.00/1.50      | ~ l1_orders_2(X0)
% 8.00/1.50      | X1 = X2 ),
% 8.00/1.50      inference(cnf_transformation,[],[f52]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1006,plain,
% 8.00/1.50      ( ~ r1_orders_2(X0,X1,X2)
% 8.00/1.50      | ~ r1_orders_2(X0,X2,X1)
% 8.00/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 8.00/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 8.00/1.50      | ~ l1_orders_2(X0)
% 8.00/1.50      | X2 = X1
% 8.00/1.50      | sK2 != X0 ),
% 8.00/1.50      inference(resolution_lifted,[status(thm)],[c_0,c_29]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1007,plain,
% 8.00/1.50      ( ~ r1_orders_2(sK2,X0,X1)
% 8.00/1.50      | ~ r1_orders_2(sK2,X1,X0)
% 8.00/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 8.00/1.50      | ~ l1_orders_2(sK2)
% 8.00/1.50      | X1 = X0 ),
% 8.00/1.50      inference(unflattening,[status(thm)],[c_1006]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1011,plain,
% 8.00/1.50      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 8.00/1.50      | ~ r1_orders_2(sK2,X1,X0)
% 8.00/1.50      | ~ r1_orders_2(sK2,X0,X1)
% 8.00/1.50      | X1 = X0 ),
% 8.00/1.50      inference(global_propositional_subsumption,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_1007,c_26]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1012,plain,
% 8.00/1.50      ( ~ r1_orders_2(sK2,X0,X1)
% 8.00/1.50      | ~ r1_orders_2(sK2,X1,X0)
% 8.00/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 8.00/1.50      | X1 = X0 ),
% 8.00/1.50      inference(renaming,[status(thm)],[c_1011]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_1255,plain,
% 8.00/1.50      ( ~ r1_orders_2(sK2,X0_47,X1_47)
% 8.00/1.50      | ~ r1_orders_2(sK2,X1_47,X0_47)
% 8.00/1.50      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 8.00/1.50      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 8.00/1.51      | X1_47 = X0_47 ),
% 8.00/1.51      inference(subtyping,[status(esa)],[c_1012]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_3655,plain,
% 8.00/1.51      ( ~ r1_orders_2(sK2,X0_47,k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)))
% 8.00/1.51      | ~ r1_orders_2(sK2,k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)),X0_47)
% 8.00/1.51      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 8.00/1.51      | ~ m1_subset_1(k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)),u1_struct_0(sK2))
% 8.00/1.51      | k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_47 ),
% 8.00/1.51      inference(instantiation,[status(thm)],[c_1255]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_3657,plain,
% 8.00/1.51      ( ~ r1_orders_2(sK2,k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)),sK3)
% 8.00/1.51      | ~ r1_orders_2(sK2,sK3,k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)))
% 8.00/1.51      | ~ m1_subset_1(k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)),u1_struct_0(sK2))
% 8.00/1.51      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 8.00/1.51      | k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3 ),
% 8.00/1.51      inference(instantiation,[status(thm)],[c_3655]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_24,negated_conjecture,
% 8.00/1.51      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 8.00/1.51      inference(cnf_transformation,[],[f81]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_1269,negated_conjecture,
% 8.00/1.51      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 8.00/1.51      inference(subtyping,[status(esa)],[c_24]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_1662,plain,
% 8.00/1.51      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 8.00/1.51      inference(predicate_to_equality,[status(thm)],[c_1269]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_2445,plain,
% 8.00/1.51      ( k13_lattice3(sK2,sK3,X0_47) = k10_lattice3(sK2,sK3,X0_47)
% 8.00/1.51      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top ),
% 8.00/1.51      inference(superposition,[status(thm)],[c_1663,c_1669]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_3407,plain,
% 8.00/1.51      ( k13_lattice3(sK2,sK3,sK4) = k10_lattice3(sK2,sK3,sK4) ),
% 8.00/1.51      inference(superposition,[status(thm)],[c_1662,c_2445]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_18,plain,
% 8.00/1.51      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
% 8.00/1.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 8.00/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 8.00/1.51      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 8.00/1.51      | ~ v2_lattice3(X0)
% 8.00/1.51      | v2_struct_0(X0)
% 8.00/1.51      | ~ v5_orders_2(X0)
% 8.00/1.51      | ~ l1_orders_2(X0) ),
% 8.00/1.51      inference(cnf_transformation,[],[f88]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_171,plain,
% 8.00/1.51      ( ~ v2_lattice3(X0)
% 8.00/1.51      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 8.00/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 8.00/1.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 8.00/1.51      | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
% 8.00/1.51      | ~ v5_orders_2(X0)
% 8.00/1.51      | ~ l1_orders_2(X0) ),
% 8.00/1.51      inference(global_propositional_subsumption,
% 8.00/1.51                [status(thm)],
% 8.00/1.51                [c_18,c_2]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_172,plain,
% 8.00/1.51      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
% 8.00/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 8.00/1.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 8.00/1.51      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 8.00/1.51      | ~ v2_lattice3(X0)
% 8.00/1.51      | ~ v5_orders_2(X0)
% 8.00/1.51      | ~ l1_orders_2(X0) ),
% 8.00/1.51      inference(renaming,[status(thm)],[c_171]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_886,plain,
% 8.00/1.51      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
% 8.00/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 8.00/1.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 8.00/1.51      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 8.00/1.51      | ~ v5_orders_2(X0)
% 8.00/1.51      | ~ l1_orders_2(X0)
% 8.00/1.51      | sK2 != X0 ),
% 8.00/1.51      inference(resolution_lifted,[status(thm)],[c_172,c_27]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_887,plain,
% 8.00/1.51      ( r1_orders_2(sK2,k11_lattice3(sK2,X0,X1),X0)
% 8.00/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 8.00/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 8.00/1.51      | ~ m1_subset_1(k11_lattice3(sK2,X0,X1),u1_struct_0(sK2))
% 8.00/1.51      | ~ v5_orders_2(sK2)
% 8.00/1.51      | ~ l1_orders_2(sK2) ),
% 8.00/1.51      inference(unflattening,[status(thm)],[c_886]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_889,plain,
% 8.00/1.51      ( r1_orders_2(sK2,k11_lattice3(sK2,X0,X1),X0)
% 8.00/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 8.00/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 8.00/1.51      | ~ m1_subset_1(k11_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
% 8.00/1.51      inference(global_propositional_subsumption,
% 8.00/1.51                [status(thm)],
% 8.00/1.51                [c_887,c_29,c_26]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_890,plain,
% 8.00/1.51      ( r1_orders_2(sK2,k11_lattice3(sK2,X0,X1),X0)
% 8.00/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 8.00/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 8.00/1.51      | ~ m1_subset_1(k11_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
% 8.00/1.51      inference(renaming,[status(thm)],[c_889]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_1073,plain,
% 8.00/1.51      ( r1_orders_2(sK2,k11_lattice3(sK2,X0,X1),X0)
% 8.00/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 8.00/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 8.00/1.51      inference(backward_subsumption_resolution,
% 8.00/1.51                [status(thm)],
% 8.00/1.51                [c_1040,c_890]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_1251,plain,
% 8.00/1.51      ( r1_orders_2(sK2,k11_lattice3(sK2,X0_47,X1_47),X0_47)
% 8.00/1.51      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 8.00/1.51      | ~ m1_subset_1(X1_47,u1_struct_0(sK2)) ),
% 8.00/1.51      inference(subtyping,[status(esa)],[c_1073]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_2772,plain,
% 8.00/1.51      ( r1_orders_2(sK2,k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)),sK3)
% 8.00/1.51      | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 8.00/1.51      | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 8.00/1.51      inference(instantiation,[status(thm)],[c_1251]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_2396,plain,
% 8.00/1.51      ( ~ r1_orders_2(sK2,X0_47,k11_lattice3(sK2,X1_47,X2_47))
% 8.00/1.51      | ~ r1_orders_2(sK2,k11_lattice3(sK2,X1_47,X2_47),X0_47)
% 8.00/1.51      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 8.00/1.51      | ~ m1_subset_1(k11_lattice3(sK2,X1_47,X2_47),u1_struct_0(sK2))
% 8.00/1.51      | X0_47 = k11_lattice3(sK2,X1_47,X2_47) ),
% 8.00/1.51      inference(instantiation,[status(thm)],[c_1255]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_2397,plain,
% 8.00/1.51      ( X0_47 = k11_lattice3(sK2,X1_47,X2_47)
% 8.00/1.51      | r1_orders_2(sK2,X0_47,k11_lattice3(sK2,X1_47,X2_47)) != iProver_top
% 8.00/1.51      | r1_orders_2(sK2,k11_lattice3(sK2,X1_47,X2_47),X0_47) != iProver_top
% 8.00/1.51      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 8.00/1.51      | m1_subset_1(k11_lattice3(sK2,X1_47,X2_47),u1_struct_0(sK2)) != iProver_top ),
% 8.00/1.51      inference(predicate_to_equality,[status(thm)],[c_2396]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_2399,plain,
% 8.00/1.51      ( sK3 = k11_lattice3(sK2,sK3,sK3)
% 8.00/1.51      | r1_orders_2(sK2,k11_lattice3(sK2,sK3,sK3),sK3) != iProver_top
% 8.00/1.51      | r1_orders_2(sK2,sK3,k11_lattice3(sK2,sK3,sK3)) != iProver_top
% 8.00/1.51      | m1_subset_1(k11_lattice3(sK2,sK3,sK3),u1_struct_0(sK2)) != iProver_top
% 8.00/1.51      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 8.00/1.51      inference(instantiation,[status(thm)],[c_2397]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_1273,plain,
% 8.00/1.51      ( X0_47 != X1_47 | X2_47 != X1_47 | X2_47 = X0_47 ),
% 8.00/1.51      theory(equality) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_2130,plain,
% 8.00/1.51      ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != X0_47
% 8.00/1.51      | sK3 != X0_47
% 8.00/1.51      | sK3 = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
% 8.00/1.51      inference(instantiation,[status(thm)],[c_1273]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_2131,plain,
% 8.00/1.51      ( k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3
% 8.00/1.51      | sK3 = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
% 8.00/1.51      | sK3 != sK3 ),
% 8.00/1.51      inference(instantiation,[status(thm)],[c_2130]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_1918,plain,
% 8.00/1.51      ( r1_orders_2(sK2,X0_47,X1_47)
% 8.00/1.51      | ~ r1_orders_2(sK2,k11_lattice3(sK2,X2_47,X3_47),X3_47)
% 8.00/1.51      | X1_47 != X3_47
% 8.00/1.51      | X0_47 != k11_lattice3(sK2,X2_47,X3_47) ),
% 8.00/1.51      inference(instantiation,[status(thm)],[c_1736]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_1920,plain,
% 8.00/1.51      ( ~ r1_orders_2(sK2,k11_lattice3(sK2,sK3,sK3),sK3)
% 8.00/1.51      | r1_orders_2(sK2,sK3,sK3)
% 8.00/1.51      | sK3 != k11_lattice3(sK2,sK3,sK3)
% 8.00/1.51      | sK3 != sK3 ),
% 8.00/1.51      inference(instantiation,[status(thm)],[c_1918]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_1879,plain,
% 8.00/1.51      ( ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 8.00/1.51      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 8.00/1.51      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
% 8.00/1.51      inference(instantiation,[status(thm)],[c_1256]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_1731,plain,
% 8.00/1.51      ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != X0_47
% 8.00/1.51      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
% 8.00/1.51      | sK3 != X0_47 ),
% 8.00/1.51      inference(instantiation,[status(thm)],[c_1273]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_1878,plain,
% 8.00/1.51      ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
% 8.00/1.51      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
% 8.00/1.51      | sK3 != k11_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
% 8.00/1.51      inference(instantiation,[status(thm)],[c_1731]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_1328,plain,
% 8.00/1.51      ( r1_orders_2(sK2,k11_lattice3(sK2,X0_47,X1_47),X0_47) = iProver_top
% 8.00/1.51      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 8.00/1.51      | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top ),
% 8.00/1.51      inference(predicate_to_equality,[status(thm)],[c_1251]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_1330,plain,
% 8.00/1.51      ( r1_orders_2(sK2,k11_lattice3(sK2,sK3,sK3),sK3) = iProver_top
% 8.00/1.51      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 8.00/1.51      inference(instantiation,[status(thm)],[c_1328]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_1329,plain,
% 8.00/1.51      ( r1_orders_2(sK2,k11_lattice3(sK2,sK3,sK3),sK3)
% 8.00/1.51      | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 8.00/1.51      inference(instantiation,[status(thm)],[c_1251]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_1325,plain,
% 8.00/1.51      ( r1_orders_2(sK2,X0_47,X1_47) != iProver_top
% 8.00/1.51      | r1_orders_2(sK2,X0_47,X2_47) != iProver_top
% 8.00/1.51      | r1_orders_2(sK2,X0_47,k11_lattice3(sK2,X1_47,X2_47)) = iProver_top
% 8.00/1.51      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 8.00/1.51      | m1_subset_1(X2_47,u1_struct_0(sK2)) != iProver_top
% 8.00/1.51      | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top ),
% 8.00/1.51      inference(predicate_to_equality,[status(thm)],[c_1252]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_1327,plain,
% 8.00/1.51      ( r1_orders_2(sK2,sK3,k11_lattice3(sK2,sK3,sK3)) = iProver_top
% 8.00/1.51      | r1_orders_2(sK2,sK3,sK3) != iProver_top
% 8.00/1.51      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 8.00/1.51      inference(instantiation,[status(thm)],[c_1325]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_1319,plain,
% 8.00/1.51      ( m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 8.00/1.51      | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top
% 8.00/1.51      | m1_subset_1(k11_lattice3(sK2,X0_47,X1_47),u1_struct_0(sK2)) = iProver_top ),
% 8.00/1.51      inference(predicate_to_equality,[status(thm)],[c_1254]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_1321,plain,
% 8.00/1.51      ( m1_subset_1(k11_lattice3(sK2,sK3,sK3),u1_struct_0(sK2)) = iProver_top
% 8.00/1.51      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 8.00/1.51      inference(instantiation,[status(thm)],[c_1319]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_23,negated_conjecture,
% 8.00/1.51      ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
% 8.00/1.51      inference(cnf_transformation,[],[f82]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_1270,negated_conjecture,
% 8.00/1.51      ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
% 8.00/1.51      inference(subtyping,[status(esa)],[c_23]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_1272,plain,( X0_47 = X0_47 ),theory(equality) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_1283,plain,
% 8.00/1.51      ( sK3 = sK3 ),
% 8.00/1.51      inference(instantiation,[status(thm)],[c_1272]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(c_36,plain,
% 8.00/1.51      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 8.00/1.51      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 8.00/1.51  
% 8.00/1.51  cnf(contradiction,plain,
% 8.00/1.51      ( $false ),
% 8.00/1.51      inference(minisat,
% 8.00/1.51                [status(thm)],
% 8.00/1.51                [c_24920,c_18528,c_7446,c_7147,c_4306,c_4295,c_3685,
% 8.00/1.51                 c_3657,c_3407,c_2772,c_2399,c_2131,c_1920,c_1879,c_1878,
% 8.00/1.51                 c_1330,c_1329,c_1327,c_1321,c_1270,c_1283,c_24,c_36,
% 8.00/1.51                 c_25]) ).
% 8.00/1.51  
% 8.00/1.51  
% 8.00/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 8.00/1.51  
% 8.00/1.51  ------                               Statistics
% 8.00/1.51  
% 8.00/1.51  ------ General
% 8.00/1.51  
% 8.00/1.51  abstr_ref_over_cycles:                  0
% 8.00/1.51  abstr_ref_under_cycles:                 0
% 8.00/1.51  gc_basic_clause_elim:                   0
% 8.00/1.51  forced_gc_time:                         0
% 8.00/1.51  parsing_time:                           0.012
% 8.00/1.51  unif_index_cands_time:                  0.
% 8.00/1.51  unif_index_add_time:                    0.
% 8.00/1.51  orderings_time:                         0.
% 8.00/1.51  out_proof_time:                         0.015
% 8.00/1.51  total_time:                             0.859
% 8.00/1.51  num_of_symbols:                         49
% 8.00/1.51  num_of_terms:                           32802
% 8.00/1.51  
% 8.00/1.51  ------ Preprocessing
% 8.00/1.51  
% 8.00/1.51  num_of_splits:                          0
% 8.00/1.51  num_of_split_atoms:                     0
% 8.00/1.51  num_of_reused_defs:                     0
% 8.00/1.51  num_eq_ax_congr_red:                    45
% 8.00/1.51  num_of_sem_filtered_clauses:            3
% 8.00/1.51  num_of_subtypes:                        3
% 8.00/1.51  monotx_restored_types:                  0
% 8.00/1.51  sat_num_of_epr_types:                   0
% 8.00/1.51  sat_num_of_non_cyclic_types:            0
% 8.00/1.51  sat_guarded_non_collapsed_types:        1
% 8.00/1.51  num_pure_diseq_elim:                    0
% 8.00/1.51  simp_replaced_by:                       0
% 8.00/1.51  res_preprocessed:                       116
% 8.00/1.51  prep_upred:                             0
% 8.00/1.51  prep_unflattend:                        21
% 8.00/1.51  smt_new_axioms:                         0
% 8.00/1.51  pred_elim_cands:                        2
% 8.00/1.51  pred_elim:                              5
% 8.00/1.51  pred_elim_cl:                           5
% 8.00/1.51  pred_elim_cycles:                       7
% 8.00/1.51  merged_defs:                            0
% 8.00/1.51  merged_defs_ncl:                        0
% 8.00/1.51  bin_hyper_res:                          0
% 8.00/1.51  prep_cycles:                            4
% 8.00/1.51  pred_elim_time:                         0.029
% 8.00/1.51  splitting_time:                         0.
% 8.00/1.51  sem_filter_time:                        0.
% 8.00/1.51  monotx_time:                            0.
% 8.00/1.51  subtype_inf_time:                       0.
% 8.00/1.51  
% 8.00/1.51  ------ Problem properties
% 8.00/1.51  
% 8.00/1.51  clauses:                                24
% 8.00/1.51  conjectures:                            3
% 8.00/1.51  epr:                                    0
% 8.00/1.51  horn:                                   18
% 8.00/1.51  ground:                                 3
% 8.00/1.51  unary:                                  3
% 8.00/1.51  binary:                                 0
% 8.00/1.51  lits:                                   106
% 8.00/1.51  lits_eq:                                14
% 8.00/1.51  fd_pure:                                0
% 8.00/1.51  fd_pseudo:                              0
% 8.00/1.51  fd_cond:                                0
% 8.00/1.51  fd_pseudo_cond:                         9
% 8.00/1.51  ac_symbols:                             0
% 8.00/1.51  
% 8.00/1.51  ------ Propositional Solver
% 8.00/1.51  
% 8.00/1.51  prop_solver_calls:                      29
% 8.00/1.51  prop_fast_solver_calls:                 1917
% 8.00/1.51  smt_solver_calls:                       0
% 8.00/1.51  smt_fast_solver_calls:                  0
% 8.00/1.51  prop_num_of_clauses:                    8594
% 8.00/1.51  prop_preprocess_simplified:             19352
% 8.00/1.51  prop_fo_subsumed:                       55
% 8.00/1.51  prop_solver_time:                       0.
% 8.00/1.51  smt_solver_time:                        0.
% 8.00/1.51  smt_fast_solver_time:                   0.
% 8.00/1.51  prop_fast_solver_time:                  0.
% 8.00/1.51  prop_unsat_core_time:                   0.001
% 8.00/1.51  
% 8.00/1.51  ------ QBF
% 8.00/1.51  
% 8.00/1.51  qbf_q_res:                              0
% 8.00/1.51  qbf_num_tautologies:                    0
% 8.00/1.51  qbf_prep_cycles:                        0
% 8.00/1.51  
% 8.00/1.51  ------ BMC1
% 8.00/1.51  
% 8.00/1.51  bmc1_current_bound:                     -1
% 8.00/1.51  bmc1_last_solved_bound:                 -1
% 8.00/1.51  bmc1_unsat_core_size:                   -1
% 8.00/1.51  bmc1_unsat_core_parents_size:           -1
% 8.00/1.51  bmc1_merge_next_fun:                    0
% 8.00/1.51  bmc1_unsat_core_clauses_time:           0.
% 8.00/1.51  
% 8.00/1.51  ------ Instantiation
% 8.00/1.51  
% 8.00/1.51  inst_num_of_clauses:                    2208
% 8.00/1.51  inst_num_in_passive:                    973
% 8.00/1.51  inst_num_in_active:                     817
% 8.00/1.51  inst_num_in_unprocessed:                417
% 8.00/1.51  inst_num_of_loops:                      1142
% 8.00/1.51  inst_num_of_learning_restarts:          0
% 8.00/1.51  inst_num_moves_active_passive:          323
% 8.00/1.51  inst_lit_activity:                      0
% 8.00/1.51  inst_lit_activity_moves:                1
% 8.00/1.51  inst_num_tautologies:                   0
% 8.00/1.51  inst_num_prop_implied:                  0
% 8.00/1.51  inst_num_existing_simplified:           0
% 8.00/1.51  inst_num_eq_res_simplified:             0
% 8.00/1.51  inst_num_child_elim:                    0
% 8.00/1.51  inst_num_of_dismatching_blockings:      1613
% 8.00/1.51  inst_num_of_non_proper_insts:           3349
% 8.00/1.51  inst_num_of_duplicates:                 0
% 8.00/1.51  inst_inst_num_from_inst_to_res:         0
% 8.00/1.51  inst_dismatching_checking_time:         0.
% 8.00/1.51  
% 8.00/1.51  ------ Resolution
% 8.00/1.51  
% 8.00/1.51  res_num_of_clauses:                     0
% 8.00/1.51  res_num_in_passive:                     0
% 8.00/1.51  res_num_in_active:                      0
% 8.00/1.51  res_num_of_loops:                       120
% 8.00/1.51  res_forward_subset_subsumed:            14
% 8.00/1.51  res_backward_subset_subsumed:           0
% 8.00/1.51  res_forward_subsumed:                   0
% 8.00/1.51  res_backward_subsumed:                  0
% 8.00/1.51  res_forward_subsumption_resolution:     0
% 8.00/1.51  res_backward_subsumption_resolution:    6
% 8.00/1.51  res_clause_to_clause_subsumption:       3371
% 8.00/1.51  res_orphan_elimination:                 0
% 8.00/1.51  res_tautology_del:                      33
% 8.00/1.51  res_num_eq_res_simplified:              0
% 8.00/1.51  res_num_sel_changes:                    0
% 8.00/1.51  res_moves_from_active_to_pass:          0
% 8.00/1.51  
% 8.00/1.51  ------ Superposition
% 8.00/1.51  
% 8.00/1.51  sup_time_total:                         0.
% 8.00/1.51  sup_time_generating:                    0.
% 8.00/1.51  sup_time_sim_full:                      0.
% 8.00/1.51  sup_time_sim_immed:                     0.
% 8.00/1.51  
% 8.00/1.51  sup_num_of_clauses:                     608
% 8.00/1.51  sup_num_in_active:                      215
% 8.00/1.51  sup_num_in_passive:                     393
% 8.00/1.51  sup_num_of_loops:                       228
% 8.00/1.51  sup_fw_superposition:                   548
% 8.00/1.51  sup_bw_superposition:                   121
% 8.00/1.51  sup_immediate_simplified:               80
% 8.00/1.51  sup_given_eliminated:                   0
% 8.00/1.51  comparisons_done:                       0
% 8.00/1.51  comparisons_avoided:                    0
% 8.00/1.51  
% 8.00/1.51  ------ Simplifications
% 8.00/1.51  
% 8.00/1.51  
% 8.00/1.51  sim_fw_subset_subsumed:                 1
% 8.00/1.51  sim_bw_subset_subsumed:                 1
% 8.00/1.51  sim_fw_subsumed:                        59
% 8.00/1.51  sim_bw_subsumed:                        0
% 8.00/1.51  sim_fw_subsumption_res:                 0
% 8.00/1.51  sim_bw_subsumption_res:                 0
% 8.00/1.51  sim_tautology_del:                      8
% 8.00/1.51  sim_eq_tautology_del:                   5
% 8.00/1.51  sim_eq_res_simp:                        0
% 8.00/1.51  sim_fw_demodulated:                     0
% 8.00/1.51  sim_bw_demodulated:                     13
% 8.00/1.51  sim_light_normalised:                   20
% 8.00/1.51  sim_joinable_taut:                      0
% 8.00/1.51  sim_joinable_simp:                      0
% 8.00/1.51  sim_ac_normalised:                      0
% 8.00/1.51  sim_smt_subsumption:                    0
% 8.00/1.51  
%------------------------------------------------------------------------------
