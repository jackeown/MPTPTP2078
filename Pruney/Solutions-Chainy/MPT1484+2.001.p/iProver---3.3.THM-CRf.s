%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:01 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 779 expanded)
%              Number of clauses        :  115 ( 214 expanded)
%              Number of leaves         :   18 ( 230 expanded)
%              Depth                    :   20
%              Number of atoms          : 1037 (4952 expanded)
%              Number of equality atoms :  190 ( 772 expanded)
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
             => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 ) ) ) ),
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
               => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2
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
              ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f33])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k13_lattice3(X0,k12_lattice3(X0,X1,sK4),sK4) != sK4
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k13_lattice3(X0,k12_lattice3(X0,sK3,X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k13_lattice3(sK2,k12_lattice3(sK2,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_orders_2(sK2)
      & v2_lattice3(sK2)
      & v1_lattice3(sK2)
      & v5_orders_2(sK2)
      & v3_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != sK4
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_orders_2(sK2)
    & v2_lattice3(sK2)
    & v1_lattice3(sK2)
    & v5_orders_2(sK2)
    & v3_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f34,f48,f47,f46])).

fof(f78,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f49])).

fof(f79,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f49])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f76,plain,(
    v2_lattice3(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f74,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f77,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

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
    inference(nnf_transformation,[],[f28])).

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
    inference(flattening,[],[f41])).

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
    inference(rectify,[],[f42])).

fof(f44,plain,(
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

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).

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
    inference(cnf_transformation,[],[f45])).

fof(f86,plain,(
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

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

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
    inference(nnf_transformation,[],[f26])).

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
    inference(flattening,[],[f36])).

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
    inference(rectify,[],[f37])).

fof(f39,plain,(
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

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).

fof(f63,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f75,plain,(
    v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f62,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f73,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f49])).

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

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f80,plain,(
    k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != sK4 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1272,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1672,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1272])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1273,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1671,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1273])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k12_lattice3(X1,X0,X2) = k12_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_27,negated_conjecture,
    ( v2_lattice3(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1007,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k12_lattice3(X1,X2,X0) = k12_lattice3(X1,X0,X2)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_27])).

cnf(c_1008,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k12_lattice3(sK2,X0,X1) = k12_lattice3(sK2,X1,X0) ),
    inference(unflattening,[status(thm)],[c_1007])).

cnf(c_29,negated_conjecture,
    ( v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_26,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1012,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k12_lattice3(sK2,X0,X1) = k12_lattice3(sK2,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1008,c_29,c_26])).

cnf(c_1013,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k12_lattice3(sK2,X1,X0) = k12_lattice3(sK2,X0,X1) ),
    inference(renaming,[status(thm)],[c_1012])).

cnf(c_1257,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
    | k12_lattice3(sK2,X1_48,X0_48) = k12_lattice3(sK2,X0_48,X1_48) ),
    inference(subtyping,[status(esa)],[c_1013])).

cnf(c_1689,plain,
    ( k12_lattice3(sK2,X0_48,X1_48) = k12_lattice3(sK2,X1_48,X0_48)
    | m1_subset_1(X1_48,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1257])).

cnf(c_2627,plain,
    ( k12_lattice3(sK2,X0_48,sK4) = k12_lattice3(sK2,sK4,X0_48)
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1671,c_1689])).

cnf(c_2742,plain,
    ( k12_lattice3(sK2,sK4,sK3) = k12_lattice3(sK2,sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1672,c_2627])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_986,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_987,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k11_lattice3(sK2,X0,X1) = k12_lattice3(sK2,X0,X1) ),
    inference(unflattening,[status(thm)],[c_986])).

cnf(c_991,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k11_lattice3(sK2,X0,X1) = k12_lattice3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_987,c_29,c_26])).

cnf(c_992,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k11_lattice3(sK2,X1,X0) = k12_lattice3(sK2,X1,X0) ),
    inference(renaming,[status(thm)],[c_991])).

cnf(c_1258,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
    | k11_lattice3(sK2,X1_48,X0_48) = k12_lattice3(sK2,X1_48,X0_48) ),
    inference(subtyping,[status(esa)],[c_992])).

cnf(c_1688,plain,
    ( k11_lattice3(sK2,X0_48,X1_48) = k12_lattice3(sK2,X0_48,X1_48)
    | m1_subset_1(X1_48,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1258])).

cnf(c_2258,plain,
    ( k11_lattice3(sK2,sK4,X0_48) = k12_lattice3(sK2,sK4,X0_48)
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1671,c_1688])).

cnf(c_2334,plain,
    ( k11_lattice3(sK2,sK4,sK3) = k12_lattice3(sK2,sK4,sK3) ),
    inference(superposition,[status(thm)],[c_1672,c_2258])).

cnf(c_2746,plain,
    ( k11_lattice3(sK2,sK4,sK3) = k12_lattice3(sK2,sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_2742,c_2334])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1086,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_26])).

cnf(c_1087,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(k11_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_1086])).

cnf(c_20,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_4,plain,
    ( ~ v2_lattice3(X0)
    | ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_169,plain,
    ( ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_4])).

cnf(c_170,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_169])).

cnf(c_966,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_170,c_27])).

cnf(c_967,plain,
    ( r1_orders_2(sK2,k11_lattice3(sK2,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(k11_lattice3(sK2,X0,X1),u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_966])).

cnf(c_969,plain,
    ( r1_orders_2(sK2,k11_lattice3(sK2,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(k11_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_967,c_29,c_26])).

cnf(c_970,plain,
    ( r1_orders_2(sK2,k11_lattice3(sK2,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(k11_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_969])).

cnf(c_1104,plain,
    ( r1_orders_2(sK2,k11_lattice3(sK2,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1087,c_970])).

cnf(c_1255,plain,
    ( r1_orders_2(sK2,k11_lattice3(sK2,X0_48,X1_48),X0_48)
    | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_48,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_1104])).

cnf(c_1691,plain,
    ( r1_orders_2(sK2,k11_lattice3(sK2,X0_48,X1_48),X0_48) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_48,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1255])).

cnf(c_4867,plain,
    ( r1_orders_2(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2746,c_1691])).

cnf(c_2259,plain,
    ( k11_lattice3(sK2,sK3,X0_48) = k12_lattice3(sK2,sK3,X0_48)
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1672,c_1688])).

cnf(c_2435,plain,
    ( k11_lattice3(sK2,sK3,sK4) = k12_lattice3(sK2,sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1671,c_2259])).

cnf(c_1256,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
    | m1_subset_1(k11_lattice3(sK2,X0_48,X1_48),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_1087])).

cnf(c_1690,plain,
    ( m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_48,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k11_lattice3(sK2,X0_48,X1_48),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1256])).

cnf(c_2920,plain,
    ( m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2435,c_1690])).

cnf(c_7,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X3,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_3,plain,
    ( ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_252,plain,
    ( ~ v1_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X2,sK0(X0,X3,X1,X2))
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7,c_3])).

cnf(c_253,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X3,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(renaming,[status(thm)],[c_252])).

cnf(c_28,negated_conjecture,
    ( v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_501,plain,
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
    inference(resolution_lifted,[status(thm)],[c_253,c_28])).

cnf(c_502,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X2,X1)
    | ~ r1_orders_2(sK2,X1,sK0(sK2,X2,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k10_lattice3(sK2,X2,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_501])).

cnf(c_506,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X2,X1)
    | ~ r1_orders_2(sK2,X1,sK0(sK2,X2,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | k10_lattice3(sK2,X2,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_502,c_29,c_26])).

cnf(c_507,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X2,X1)
    | ~ r1_orders_2(sK2,X1,sK0(sK2,X2,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k10_lattice3(sK2,X2,X0) = X1 ),
    inference(renaming,[status(thm)],[c_506])).

cnf(c_1270,plain,
    ( ~ r1_orders_2(sK2,X0_48,X1_48)
    | ~ r1_orders_2(sK2,X2_48,X1_48)
    | ~ r1_orders_2(sK2,X1_48,sK0(sK2,X2_48,X0_48,X1_48))
    | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
    | ~ m1_subset_1(X2_48,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | k10_lattice3(sK2,X2_48,X0_48) = X1_48 ),
    inference(subtyping,[status(esa)],[c_507])).

cnf(c_2113,plain,
    ( ~ r1_orders_2(sK2,X0_48,sK0(sK2,k12_lattice3(sK2,sK3,sK4),sK4,X0_48))
    | ~ r1_orders_2(sK2,k12_lattice3(sK2,sK3,sK4),X0_48)
    | ~ r1_orders_2(sK2,sK4,X0_48)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | ~ m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = X0_48 ),
    inference(instantiation,[status(thm)],[c_1270])).

cnf(c_2129,plain,
    ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = X0_48
    | r1_orders_2(sK2,X0_48,sK0(sK2,k12_lattice3(sK2,sK3,sK4),sK4,X0_48)) != iProver_top
    | r1_orders_2(sK2,k12_lattice3(sK2,sK3,sK4),X0_48) != iProver_top
    | r1_orders_2(sK2,sK4,X0_48) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2113])).

cnf(c_2131,plain,
    ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = sK4
    | r1_orders_2(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != iProver_top
    | r1_orders_2(sK2,sK4,sK0(sK2,k12_lattice3(sK2,sK3,sK4),sK4,sK4)) != iProver_top
    | r1_orders_2(sK2,sK4,sK4) != iProver_top
    | m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2129])).

cnf(c_8,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X1,sK0(X0,X3,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_247,plain,
    ( ~ v1_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_orders_2(X0,X1,sK0(X0,X3,X1,X2))
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_3])).

cnf(c_248,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,X1,sK0(X0,X3,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X3,X1) = X2 ),
    inference(renaming,[status(thm)],[c_247])).

cnf(c_534,plain,
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
    inference(resolution_lifted,[status(thm)],[c_248,c_28])).

cnf(c_535,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X2,X1)
    | r1_orders_2(sK2,X0,sK0(sK2,X2,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k10_lattice3(sK2,X2,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_534])).

cnf(c_539,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X2,X1)
    | r1_orders_2(sK2,X0,sK0(sK2,X2,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | k10_lattice3(sK2,X2,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_535,c_29,c_26])).

cnf(c_540,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X2,X1)
    | r1_orders_2(sK2,X0,sK0(sK2,X2,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k10_lattice3(sK2,X2,X0) = X1 ),
    inference(renaming,[status(thm)],[c_539])).

cnf(c_1269,plain,
    ( ~ r1_orders_2(sK2,X0_48,X1_48)
    | ~ r1_orders_2(sK2,X2_48,X1_48)
    | r1_orders_2(sK2,X0_48,sK0(sK2,X2_48,X0_48,X1_48))
    | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
    | ~ m1_subset_1(X2_48,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | k10_lattice3(sK2,X2_48,X0_48) = X1_48 ),
    inference(subtyping,[status(esa)],[c_540])).

cnf(c_2114,plain,
    ( ~ r1_orders_2(sK2,k12_lattice3(sK2,sK3,sK4),X0_48)
    | ~ r1_orders_2(sK2,sK4,X0_48)
    | r1_orders_2(sK2,sK4,sK0(sK2,k12_lattice3(sK2,sK3,sK4),sK4,X0_48))
    | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | ~ m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = X0_48 ),
    inference(instantiation,[status(thm)],[c_1269])).

cnf(c_2125,plain,
    ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = X0_48
    | r1_orders_2(sK2,k12_lattice3(sK2,sK3,sK4),X0_48) != iProver_top
    | r1_orders_2(sK2,sK4,X0_48) != iProver_top
    | r1_orders_2(sK2,sK4,sK0(sK2,k12_lattice3(sK2,sK3,sK4),sK4,X0_48)) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2114])).

cnf(c_2127,plain,
    ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = sK4
    | r1_orders_2(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != iProver_top
    | r1_orders_2(sK2,sK4,sK0(sK2,k12_lattice3(sK2,sK3,sK4),sK4,sK4)) = iProver_top
    | r1_orders_2(sK2,sK4,sK4) != iProver_top
    | m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2125])).

cnf(c_1280,plain,
    ( X0_48 != X1_48
    | X2_48 != X1_48
    | X2_48 = X0_48 ),
    theory(equality)).

cnf(c_2030,plain,
    ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != X0_48
    | sK4 != X0_48
    | sK4 = k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_1280])).

cnf(c_2031,plain,
    ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != sK4
    | sK4 = k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2030])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k13_lattice3(X1,X2,X0) = k10_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_706,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k13_lattice3(X1,X2,X0) = k10_lattice3(X1,X2,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_28])).

cnf(c_707,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k13_lattice3(sK2,X0,X1) = k10_lattice3(sK2,X0,X1) ),
    inference(unflattening,[status(thm)],[c_706])).

cnf(c_711,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k13_lattice3(sK2,X0,X1) = k10_lattice3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_707,c_29,c_26])).

cnf(c_712,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k13_lattice3(sK2,X1,X0) = k10_lattice3(sK2,X1,X0) ),
    inference(renaming,[status(thm)],[c_711])).

cnf(c_1263,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
    | k13_lattice3(sK2,X1_48,X0_48) = k10_lattice3(sK2,X1_48,X0_48) ),
    inference(subtyping,[status(esa)],[c_712])).

cnf(c_1984,plain,
    ( ~ m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_1263])).

cnf(c_1985,plain,
    ( k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4)
    | m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1984])).

cnf(c_1973,plain,
    ( k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != X0_48
    | k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = sK4
    | sK4 != X0_48 ),
    inference(instantiation,[status(thm)],[c_1280])).

cnf(c_1983,plain,
    ( k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4)
    | k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = sK4
    | sK4 != k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_1973])).

cnf(c_2,plain,
    ( r3_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_30,negated_conjecture,
    ( v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_398,plain,
    ( r3_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_30])).

cnf(c_399,plain,
    ( r3_orders_2(sK2,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_85,plain,
    ( ~ v2_lattice3(sK2)
    | ~ v2_struct_0(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_403,plain,
    ( r3_orders_2(sK2,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_399,c_27,c_26,c_85])).

cnf(c_404,plain,
    ( r3_orders_2(sK2,X0,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_403])).

cnf(c_1,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_419,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_30])).

cnf(c_420,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ r3_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_419])).

cnf(c_424,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ r3_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_420,c_27,c_26,c_85])).

cnf(c_425,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ r3_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_424])).

cnf(c_482,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X3,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | X0 != X3
    | X1 != X3
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_404,c_425])).

cnf(c_483,plain,
    ( r1_orders_2(sK2,X0,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_1271,plain,
    ( r1_orders_2(sK2,X0_48,X0_48)
    | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_48,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_483])).

cnf(c_1275,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1271])).

cnf(c_1297,plain,
    ( m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1275])).

cnf(c_1299,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_1297])).

cnf(c_1276,plain,
    ( r1_orders_2(sK2,X0_48,X0_48)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_1271])).

cnf(c_1294,plain,
    ( r1_orders_2(sK2,X0_48,X0_48) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1276])).

cnf(c_1296,plain,
    ( r1_orders_2(sK2,sK4,sK4) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_1294])).

cnf(c_1277,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1271])).

cnf(c_1293,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1277])).

cnf(c_23,negated_conjecture,
    ( k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != sK4 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1274,negated_conjecture,
    ( k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != sK4 ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1279,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_1290,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1279])).

cnf(c_37,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_36,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4867,c_2920,c_2131,c_2127,c_2031,c_1985,c_1983,c_1299,c_1296,c_1293,c_1274,c_1290,c_37,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:09:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
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
% 2.97/1.00  clauses                                 24
% 2.97/1.00  conjectures                             3
% 2.97/1.00  EPR                                     1
% 2.97/1.00  Horn                                    17
% 2.97/1.00  unary                                   3
% 2.97/1.00  binary                                  2
% 2.97/1.00  lits                                    105
% 2.97/1.00  lits eq                                 12
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
% 2.97/1.00  fof(f11,conjecture,(
% 2.97/1.00    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2)))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f12,negated_conjecture,(
% 2.97/1.00    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2)))),
% 2.97/1.00    inference(negated_conjecture,[],[f11])).
% 2.97/1.00  
% 2.97/1.00  fof(f33,plain,(
% 2.97/1.00    ? [X0] : (? [X1] : (? [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)))),
% 2.97/1.00    inference(ennf_transformation,[],[f12])).
% 2.97/1.00  
% 2.97/1.00  fof(f34,plain,(
% 2.97/1.00    ? [X0] : (? [X1] : (? [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 2.97/1.00    inference(flattening,[],[f33])).
% 2.97/1.00  
% 2.97/1.00  fof(f48,plain,(
% 2.97/1.00    ( ! [X0,X1] : (? [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) => (k13_lattice3(X0,k12_lattice3(X0,X1,sK4),sK4) != sK4 & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 2.97/1.00    introduced(choice_axiom,[])).
% 2.97/1.00  
% 2.97/1.00  fof(f47,plain,(
% 2.97/1.00    ( ! [X0] : (? [X1] : (? [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k13_lattice3(X0,k12_lattice3(X0,sK3,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 2.97/1.00    introduced(choice_axiom,[])).
% 2.97/1.00  
% 2.97/1.00  fof(f46,plain,(
% 2.97/1.00    ? [X0] : (? [X1] : (? [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => (? [X1] : (? [X2] : (k13_lattice3(sK2,k12_lattice3(sK2,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_orders_2(sK2) & v2_lattice3(sK2) & v1_lattice3(sK2) & v5_orders_2(sK2) & v3_orders_2(sK2))),
% 2.97/1.00    introduced(choice_axiom,[])).
% 2.97/1.00  
% 2.97/1.00  fof(f49,plain,(
% 2.97/1.00    ((k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != sK4 & m1_subset_1(sK4,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_orders_2(sK2) & v2_lattice3(sK2) & v1_lattice3(sK2) & v5_orders_2(sK2) & v3_orders_2(sK2)),
% 2.97/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f34,f48,f47,f46])).
% 2.97/1.00  
% 2.97/1.00  fof(f78,plain,(
% 2.97/1.00    m1_subset_1(sK3,u1_struct_0(sK2))),
% 2.97/1.00    inference(cnf_transformation,[],[f49])).
% 2.97/1.00  
% 2.97/1.00  fof(f79,plain,(
% 2.97/1.00    m1_subset_1(sK4,u1_struct_0(sK2))),
% 2.97/1.00    inference(cnf_transformation,[],[f49])).
% 2.97/1.00  
% 2.97/1.00  fof(f5,axiom,(
% 2.97/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f21,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 2.97/1.00    inference(ennf_transformation,[],[f5])).
% 2.97/1.00  
% 2.97/1.00  fof(f22,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 2.97/1.00    inference(flattening,[],[f21])).
% 2.97/1.00  
% 2.97/1.00  fof(f55,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f22])).
% 2.97/1.00  
% 2.97/1.00  fof(f76,plain,(
% 2.97/1.00    v2_lattice3(sK2)),
% 2.97/1.00    inference(cnf_transformation,[],[f49])).
% 2.97/1.00  
% 2.97/1.00  fof(f74,plain,(
% 2.97/1.00    v5_orders_2(sK2)),
% 2.97/1.00    inference(cnf_transformation,[],[f49])).
% 2.97/1.00  
% 2.97/1.00  fof(f77,plain,(
% 2.97/1.00    l1_orders_2(sK2)),
% 2.97/1.00    inference(cnf_transformation,[],[f49])).
% 2.97/1.00  
% 2.97/1.00  fof(f9,axiom,(
% 2.97/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f29,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 2.97/1.00    inference(ennf_transformation,[],[f9])).
% 2.97/1.00  
% 2.97/1.00  fof(f30,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 2.97/1.00    inference(flattening,[],[f29])).
% 2.97/1.00  
% 2.97/1.00  fof(f71,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f30])).
% 2.97/1.00  
% 2.97/1.00  fof(f6,axiom,(
% 2.97/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f23,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 2.97/1.00    inference(ennf_transformation,[],[f6])).
% 2.97/1.00  
% 2.97/1.00  fof(f24,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 2.97/1.00    inference(flattening,[],[f23])).
% 2.97/1.00  
% 2.97/1.00  fof(f56,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f24])).
% 2.97/1.00  
% 2.97/1.00  fof(f8,axiom,(
% 2.97/1.00    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f27,plain,(
% 2.97/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 2.97/1.00    inference(ennf_transformation,[],[f8])).
% 2.97/1.00  
% 2.97/1.00  fof(f28,plain,(
% 2.97/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.97/1.00    inference(flattening,[],[f27])).
% 2.97/1.00  
% 2.97/1.00  fof(f41,plain,(
% 2.97/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.97/1.00    inference(nnf_transformation,[],[f28])).
% 2.97/1.00  
% 2.97/1.00  fof(f42,plain,(
% 2.97/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.97/1.00    inference(flattening,[],[f41])).
% 2.97/1.00  
% 2.97/1.00  fof(f43,plain,(
% 2.97/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.97/1.00    inference(rectify,[],[f42])).
% 2.97/1.00  
% 2.97/1.00  fof(f44,plain,(
% 2.97/1.00    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK1(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X1) & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0))))),
% 2.97/1.00    introduced(choice_axiom,[])).
% 2.97/1.00  
% 2.97/1.00  fof(f45,plain,(
% 2.97/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,sK1(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X1) & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.97/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).
% 2.97/1.00  
% 2.97/1.00  fof(f64,plain,(
% 2.97/1.00    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X3,X1) | k11_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f45])).
% 2.97/1.00  
% 2.97/1.00  fof(f86,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1) | ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.97/1.00    inference(equality_resolution,[],[f64])).
% 2.97/1.00  
% 2.97/1.00  fof(f4,axiom,(
% 2.97/1.00    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f19,plain,(
% 2.97/1.00    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 2.97/1.00    inference(ennf_transformation,[],[f4])).
% 2.97/1.00  
% 2.97/1.00  fof(f20,plain,(
% 2.97/1.00    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 2.97/1.00    inference(flattening,[],[f19])).
% 2.97/1.00  
% 2.97/1.00  fof(f54,plain,(
% 2.97/1.00    ( ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f20])).
% 2.97/1.00  
% 2.97/1.00  fof(f7,axiom,(
% 2.97/1.00    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f25,plain,(
% 2.97/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 2.97/1.00    inference(ennf_transformation,[],[f7])).
% 2.97/1.00  
% 2.97/1.00  fof(f26,plain,(
% 2.97/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.97/1.00    inference(flattening,[],[f25])).
% 2.97/1.00  
% 2.97/1.00  fof(f36,plain,(
% 2.97/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3))) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.97/1.00    inference(nnf_transformation,[],[f26])).
% 2.97/1.00  
% 2.97/1.00  fof(f37,plain,(
% 2.97/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.97/1.00    inference(flattening,[],[f36])).
% 2.97/1.00  
% 2.97/1.00  fof(f38,plain,(
% 2.97/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.97/1.00    inference(rectify,[],[f37])).
% 2.97/1.00  
% 2.97/1.00  fof(f39,plain,(
% 2.97/1.00    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,X3,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))))),
% 2.97/1.00    introduced(choice_axiom,[])).
% 2.97/1.00  
% 2.97/1.00  fof(f40,plain,(
% 2.97/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,X3,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.97/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).
% 2.97/1.00  
% 2.97/1.00  fof(f63,plain,(
% 2.97/1.00    ( ! [X2,X0,X3,X1] : (k10_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,X3,sK0(X0,X1,X2,X3)) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f40])).
% 2.97/1.00  
% 2.97/1.00  fof(f3,axiom,(
% 2.97/1.00    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f17,plain,(
% 2.97/1.00    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 2.97/1.00    inference(ennf_transformation,[],[f3])).
% 2.97/1.00  
% 2.97/1.00  fof(f18,plain,(
% 2.97/1.00    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 2.97/1.00    inference(flattening,[],[f17])).
% 2.97/1.00  
% 2.97/1.00  fof(f53,plain,(
% 2.97/1.00    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f18])).
% 2.97/1.00  
% 2.97/1.00  fof(f75,plain,(
% 2.97/1.00    v1_lattice3(sK2)),
% 2.97/1.00    inference(cnf_transformation,[],[f49])).
% 2.97/1.00  
% 2.97/1.00  fof(f62,plain,(
% 2.97/1.00    ( ! [X2,X0,X3,X1] : (k10_lattice3(X0,X1,X2) = X3 | r1_orders_2(X0,X2,sK0(X0,X1,X2,X3)) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f40])).
% 2.97/1.00  
% 2.97/1.00  fof(f10,axiom,(
% 2.97/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f31,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 2.97/1.00    inference(ennf_transformation,[],[f10])).
% 2.97/1.00  
% 2.97/1.00  fof(f32,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 2.97/1.00    inference(flattening,[],[f31])).
% 2.97/1.00  
% 2.97/1.00  fof(f72,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f32])).
% 2.97/1.00  
% 2.97/1.00  fof(f2,axiom,(
% 2.97/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => r3_orders_2(X0,X1,X1))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f15,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.97/1.00    inference(ennf_transformation,[],[f2])).
% 2.97/1.00  
% 2.97/1.00  fof(f16,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.97/1.00    inference(flattening,[],[f15])).
% 2.97/1.00  
% 2.97/1.00  fof(f52,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f16])).
% 2.97/1.00  
% 2.97/1.00  fof(f73,plain,(
% 2.97/1.00    v3_orders_2(sK2)),
% 2.97/1.00    inference(cnf_transformation,[],[f49])).
% 2.97/1.00  
% 2.97/1.00  fof(f1,axiom,(
% 2.97/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f13,plain,(
% 2.97/1.00    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.97/1.00    inference(ennf_transformation,[],[f1])).
% 2.97/1.00  
% 2.97/1.00  fof(f14,plain,(
% 2.97/1.00    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.97/1.00    inference(flattening,[],[f13])).
% 2.97/1.00  
% 2.97/1.00  fof(f35,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.97/1.00    inference(nnf_transformation,[],[f14])).
% 2.97/1.00  
% 2.97/1.00  fof(f50,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f35])).
% 2.97/1.00  
% 2.97/1.00  fof(f80,plain,(
% 2.97/1.00    k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != sK4),
% 2.97/1.00    inference(cnf_transformation,[],[f49])).
% 2.97/1.00  
% 2.97/1.00  cnf(c_25,negated_conjecture,
% 2.97/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.97/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1272,negated_conjecture,
% 2.97/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.97/1.00      inference(subtyping,[status(esa)],[c_25]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1672,plain,
% 2.97/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_1272]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_24,negated_conjecture,
% 2.97/1.00      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 2.97/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1273,negated_conjecture,
% 2.97/1.00      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 2.97/1.00      inference(subtyping,[status(esa)],[c_24]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1671,plain,
% 2.97/1.00      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_1273]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_5,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.97/1.00      | ~ v5_orders_2(X1)
% 2.97/1.00      | ~ v2_lattice3(X1)
% 2.97/1.00      | ~ l1_orders_2(X1)
% 2.97/1.00      | k12_lattice3(X1,X0,X2) = k12_lattice3(X1,X2,X0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_27,negated_conjecture,
% 2.97/1.00      ( v2_lattice3(sK2) ),
% 2.97/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1007,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.97/1.00      | ~ v5_orders_2(X1)
% 2.97/1.00      | ~ l1_orders_2(X1)
% 2.97/1.00      | k12_lattice3(X1,X2,X0) = k12_lattice3(X1,X0,X2)
% 2.97/1.00      | sK2 != X1 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_27]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1008,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | ~ v5_orders_2(sK2)
% 2.97/1.00      | ~ l1_orders_2(sK2)
% 2.97/1.00      | k12_lattice3(sK2,X0,X1) = k12_lattice3(sK2,X1,X0) ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_1007]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_29,negated_conjecture,
% 2.97/1.00      ( v5_orders_2(sK2) ),
% 2.97/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_26,negated_conjecture,
% 2.97/1.00      ( l1_orders_2(sK2) ),
% 2.97/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1012,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | k12_lattice3(sK2,X0,X1) = k12_lattice3(sK2,X1,X0) ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_1008,c_29,c_26]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1013,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | k12_lattice3(sK2,X1,X0) = k12_lattice3(sK2,X0,X1) ),
% 2.97/1.00      inference(renaming,[status(thm)],[c_1012]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1257,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0_48,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
% 2.97/1.00      | k12_lattice3(sK2,X1_48,X0_48) = k12_lattice3(sK2,X0_48,X1_48) ),
% 2.97/1.00      inference(subtyping,[status(esa)],[c_1013]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1689,plain,
% 2.97/1.00      ( k12_lattice3(sK2,X0_48,X1_48) = k12_lattice3(sK2,X1_48,X0_48)
% 2.97/1.00      | m1_subset_1(X1_48,u1_struct_0(sK2)) != iProver_top
% 2.97/1.00      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_1257]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2627,plain,
% 2.97/1.00      ( k12_lattice3(sK2,X0_48,sK4) = k12_lattice3(sK2,sK4,X0_48)
% 2.97/1.00      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_1671,c_1689]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2742,plain,
% 2.97/1.00      ( k12_lattice3(sK2,sK4,sK3) = k12_lattice3(sK2,sK3,sK4) ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_1672,c_2627]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_21,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.97/1.00      | ~ v5_orders_2(X1)
% 2.97/1.00      | ~ v2_lattice3(X1)
% 2.97/1.00      | ~ l1_orders_2(X1)
% 2.97/1.00      | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_986,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.97/1.00      | ~ v5_orders_2(X1)
% 2.97/1.00      | ~ l1_orders_2(X1)
% 2.97/1.00      | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0)
% 2.97/1.00      | sK2 != X1 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_987,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | ~ v5_orders_2(sK2)
% 2.97/1.00      | ~ l1_orders_2(sK2)
% 2.97/1.00      | k11_lattice3(sK2,X0,X1) = k12_lattice3(sK2,X0,X1) ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_986]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_991,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | k11_lattice3(sK2,X0,X1) = k12_lattice3(sK2,X0,X1) ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_987,c_29,c_26]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_992,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | k11_lattice3(sK2,X1,X0) = k12_lattice3(sK2,X1,X0) ),
% 2.97/1.00      inference(renaming,[status(thm)],[c_991]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1258,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0_48,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
% 2.97/1.00      | k11_lattice3(sK2,X1_48,X0_48) = k12_lattice3(sK2,X1_48,X0_48) ),
% 2.97/1.00      inference(subtyping,[status(esa)],[c_992]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1688,plain,
% 2.97/1.00      ( k11_lattice3(sK2,X0_48,X1_48) = k12_lattice3(sK2,X0_48,X1_48)
% 2.97/1.00      | m1_subset_1(X1_48,u1_struct_0(sK2)) != iProver_top
% 2.97/1.00      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_1258]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2258,plain,
% 2.97/1.00      ( k11_lattice3(sK2,sK4,X0_48) = k12_lattice3(sK2,sK4,X0_48)
% 2.97/1.00      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_1671,c_1688]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2334,plain,
% 2.97/1.00      ( k11_lattice3(sK2,sK4,sK3) = k12_lattice3(sK2,sK4,sK3) ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_1672,c_2258]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2746,plain,
% 2.97/1.00      ( k11_lattice3(sK2,sK4,sK3) = k12_lattice3(sK2,sK3,sK4) ),
% 2.97/1.00      inference(demodulation,[status(thm)],[c_2742,c_2334]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_6,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.97/1.00      | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
% 2.97/1.00      | ~ l1_orders_2(X1) ),
% 2.97/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1086,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.97/1.00      | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
% 2.97/1.00      | sK2 != X1 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_26]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1087,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | m1_subset_1(k11_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_1086]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_20,plain,
% 2.97/1.00      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.97/1.00      | ~ v5_orders_2(X0)
% 2.97/1.00      | ~ v2_lattice3(X0)
% 2.97/1.00      | v2_struct_0(X0)
% 2.97/1.00      | ~ l1_orders_2(X0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f86]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_4,plain,
% 2.97/1.00      ( ~ v2_lattice3(X0) | ~ v2_struct_0(X0) | ~ l1_orders_2(X0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_169,plain,
% 2.97/1.00      ( ~ v2_lattice3(X0)
% 2.97/1.00      | ~ v5_orders_2(X0)
% 2.97/1.00      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.00      | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
% 2.97/1.00      | ~ l1_orders_2(X0) ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_20,c_4]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_170,plain,
% 2.97/1.00      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.97/1.00      | ~ v5_orders_2(X0)
% 2.97/1.00      | ~ v2_lattice3(X0)
% 2.97/1.00      | ~ l1_orders_2(X0) ),
% 2.97/1.00      inference(renaming,[status(thm)],[c_169]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_966,plain,
% 2.97/1.00      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.97/1.00      | ~ v5_orders_2(X0)
% 2.97/1.00      | ~ l1_orders_2(X0)
% 2.97/1.00      | sK2 != X0 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_170,c_27]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_967,plain,
% 2.97/1.00      ( r1_orders_2(sK2,k11_lattice3(sK2,X0,X1),X0)
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(k11_lattice3(sK2,X0,X1),u1_struct_0(sK2))
% 2.97/1.00      | ~ v5_orders_2(sK2)
% 2.97/1.00      | ~ l1_orders_2(sK2) ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_966]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_969,plain,
% 2.97/1.00      ( r1_orders_2(sK2,k11_lattice3(sK2,X0,X1),X0)
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(k11_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_967,c_29,c_26]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_970,plain,
% 2.97/1.00      ( r1_orders_2(sK2,k11_lattice3(sK2,X0,X1),X0)
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(k11_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
% 2.97/1.00      inference(renaming,[status(thm)],[c_969]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1104,plain,
% 2.97/1.00      ( r1_orders_2(sK2,k11_lattice3(sK2,X0,X1),X0)
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 2.97/1.00      inference(backward_subsumption_resolution,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_1087,c_970]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1255,plain,
% 2.97/1.00      ( r1_orders_2(sK2,k11_lattice3(sK2,X0_48,X1_48),X0_48)
% 2.97/1.00      | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X0_48,u1_struct_0(sK2)) ),
% 2.97/1.00      inference(subtyping,[status(esa)],[c_1104]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1691,plain,
% 2.97/1.00      ( r1_orders_2(sK2,k11_lattice3(sK2,X0_48,X1_48),X0_48) = iProver_top
% 2.97/1.00      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
% 2.97/1.00      | m1_subset_1(X1_48,u1_struct_0(sK2)) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_1255]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_4867,plain,
% 2.97/1.00      ( r1_orders_2(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = iProver_top
% 2.97/1.00      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 2.97/1.00      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_2746,c_1691]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2259,plain,
% 2.97/1.00      ( k11_lattice3(sK2,sK3,X0_48) = k12_lattice3(sK2,sK3,X0_48)
% 2.97/1.00      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_1672,c_1688]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2435,plain,
% 2.97/1.00      ( k11_lattice3(sK2,sK3,sK4) = k12_lattice3(sK2,sK3,sK4) ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_1671,c_2259]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1256,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0_48,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
% 2.97/1.00      | m1_subset_1(k11_lattice3(sK2,X0_48,X1_48),u1_struct_0(sK2)) ),
% 2.97/1.00      inference(subtyping,[status(esa)],[c_1087]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1690,plain,
% 2.97/1.00      ( m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
% 2.97/1.00      | m1_subset_1(X1_48,u1_struct_0(sK2)) != iProver_top
% 2.97/1.00      | m1_subset_1(k11_lattice3(sK2,X0_48,X1_48),u1_struct_0(sK2)) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_1256]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2920,plain,
% 2.97/1.00      ( m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) = iProver_top
% 2.97/1.00      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 2.97/1.00      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_2435,c_1690]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_7,plain,
% 2.97/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 2.97/1.00      | ~ r1_orders_2(X0,X3,X2)
% 2.97/1.00      | ~ r1_orders_2(X0,X2,sK0(X0,X3,X1,X2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.00      | ~ v5_orders_2(X0)
% 2.97/1.00      | ~ v1_lattice3(X0)
% 2.97/1.00      | v2_struct_0(X0)
% 2.97/1.00      | ~ l1_orders_2(X0)
% 2.97/1.00      | k10_lattice3(X0,X3,X1) = X2 ),
% 2.97/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_3,plain,
% 2.97/1.00      ( ~ v1_lattice3(X0) | ~ v2_struct_0(X0) | ~ l1_orders_2(X0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_252,plain,
% 2.97/1.00      ( ~ v1_lattice3(X0)
% 2.97/1.00      | ~ v5_orders_2(X0)
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | ~ r1_orders_2(X0,X2,sK0(X0,X3,X1,X2))
% 2.97/1.00      | ~ r1_orders_2(X0,X3,X2)
% 2.97/1.00      | ~ r1_orders_2(X0,X1,X2)
% 2.97/1.00      | ~ l1_orders_2(X0)
% 2.97/1.00      | k10_lattice3(X0,X3,X1) = X2 ),
% 2.97/1.00      inference(global_propositional_subsumption,[status(thm)],[c_7,c_3]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_253,plain,
% 2.97/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 2.97/1.00      | ~ r1_orders_2(X0,X3,X2)
% 2.97/1.00      | ~ r1_orders_2(X0,X2,sK0(X0,X3,X1,X2))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.97/1.00      | ~ v5_orders_2(X0)
% 2.97/1.00      | ~ v1_lattice3(X0)
% 2.97/1.00      | ~ l1_orders_2(X0)
% 2.97/1.00      | k10_lattice3(X0,X3,X1) = X2 ),
% 2.97/1.00      inference(renaming,[status(thm)],[c_252]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_28,negated_conjecture,
% 2.97/1.00      ( v1_lattice3(sK2) ),
% 2.97/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_501,plain,
% 2.97/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 2.97/1.00      | ~ r1_orders_2(X0,X3,X2)
% 2.97/1.00      | ~ r1_orders_2(X0,X2,sK0(X0,X3,X1,X2))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.97/1.00      | ~ v5_orders_2(X0)
% 2.97/1.00      | ~ l1_orders_2(X0)
% 2.97/1.00      | k10_lattice3(X0,X3,X1) = X2
% 2.97/1.00      | sK2 != X0 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_253,c_28]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_502,plain,
% 2.97/1.00      ( ~ r1_orders_2(sK2,X0,X1)
% 2.97/1.00      | ~ r1_orders_2(sK2,X2,X1)
% 2.97/1.00      | ~ r1_orders_2(sK2,X1,sK0(sK2,X2,X0,X1))
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 2.97/1.00      | ~ v5_orders_2(sK2)
% 2.97/1.00      | ~ l1_orders_2(sK2)
% 2.97/1.00      | k10_lattice3(sK2,X2,X0) = X1 ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_501]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_506,plain,
% 2.97/1.00      ( ~ r1_orders_2(sK2,X0,X1)
% 2.97/1.00      | ~ r1_orders_2(sK2,X2,X1)
% 2.97/1.00      | ~ r1_orders_2(sK2,X1,sK0(sK2,X2,X0,X1))
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 2.97/1.00      | k10_lattice3(sK2,X2,X0) = X1 ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_502,c_29,c_26]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_507,plain,
% 2.97/1.00      ( ~ r1_orders_2(sK2,X0,X1)
% 2.97/1.00      | ~ r1_orders_2(sK2,X2,X1)
% 2.97/1.00      | ~ r1_orders_2(sK2,X1,sK0(sK2,X2,X0,X1))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | k10_lattice3(sK2,X2,X0) = X1 ),
% 2.97/1.00      inference(renaming,[status(thm)],[c_506]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1270,plain,
% 2.97/1.00      ( ~ r1_orders_2(sK2,X0_48,X1_48)
% 2.97/1.00      | ~ r1_orders_2(sK2,X2_48,X1_48)
% 2.97/1.00      | ~ r1_orders_2(sK2,X1_48,sK0(sK2,X2_48,X0_48,X1_48))
% 2.97/1.00      | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X2_48,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
% 2.97/1.00      | k10_lattice3(sK2,X2_48,X0_48) = X1_48 ),
% 2.97/1.00      inference(subtyping,[status(esa)],[c_507]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2113,plain,
% 2.97/1.00      ( ~ r1_orders_2(sK2,X0_48,sK0(sK2,k12_lattice3(sK2,sK3,sK4),sK4,X0_48))
% 2.97/1.00      | ~ r1_orders_2(sK2,k12_lattice3(sK2,sK3,sK4),X0_48)
% 2.97/1.00      | ~ r1_orders_2(sK2,sK4,X0_48)
% 2.97/1.00      | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 2.97/1.00      | k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = X0_48 ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_1270]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2129,plain,
% 2.97/1.00      ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = X0_48
% 2.97/1.00      | r1_orders_2(sK2,X0_48,sK0(sK2,k12_lattice3(sK2,sK3,sK4),sK4,X0_48)) != iProver_top
% 2.97/1.00      | r1_orders_2(sK2,k12_lattice3(sK2,sK3,sK4),X0_48) != iProver_top
% 2.97/1.00      | r1_orders_2(sK2,sK4,X0_48) != iProver_top
% 2.97/1.00      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
% 2.97/1.00      | m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 2.97/1.00      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_2113]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2131,plain,
% 2.97/1.00      ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = sK4
% 2.97/1.00      | r1_orders_2(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != iProver_top
% 2.97/1.00      | r1_orders_2(sK2,sK4,sK0(sK2,k12_lattice3(sK2,sK3,sK4),sK4,sK4)) != iProver_top
% 2.97/1.00      | r1_orders_2(sK2,sK4,sK4) != iProver_top
% 2.97/1.00      | m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 2.97/1.00      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_2129]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_8,plain,
% 2.97/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 2.97/1.00      | ~ r1_orders_2(X0,X3,X2)
% 2.97/1.00      | r1_orders_2(X0,X1,sK0(X0,X3,X1,X2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.00      | ~ v5_orders_2(X0)
% 2.97/1.00      | ~ v1_lattice3(X0)
% 2.97/1.00      | v2_struct_0(X0)
% 2.97/1.00      | ~ l1_orders_2(X0)
% 2.97/1.00      | k10_lattice3(X0,X3,X1) = X2 ),
% 2.97/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_247,plain,
% 2.97/1.00      ( ~ v1_lattice3(X0)
% 2.97/1.00      | ~ v5_orders_2(X0)
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | r1_orders_2(X0,X1,sK0(X0,X3,X1,X2))
% 2.97/1.00      | ~ r1_orders_2(X0,X3,X2)
% 2.97/1.00      | ~ r1_orders_2(X0,X1,X2)
% 2.97/1.00      | ~ l1_orders_2(X0)
% 2.97/1.00      | k10_lattice3(X0,X3,X1) = X2 ),
% 2.97/1.00      inference(global_propositional_subsumption,[status(thm)],[c_8,c_3]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_248,plain,
% 2.97/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 2.97/1.00      | ~ r1_orders_2(X0,X3,X2)
% 2.97/1.00      | r1_orders_2(X0,X1,sK0(X0,X3,X1,X2))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.97/1.00      | ~ v5_orders_2(X0)
% 2.97/1.00      | ~ v1_lattice3(X0)
% 2.97/1.00      | ~ l1_orders_2(X0)
% 2.97/1.00      | k10_lattice3(X0,X3,X1) = X2 ),
% 2.97/1.00      inference(renaming,[status(thm)],[c_247]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_534,plain,
% 2.97/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 2.97/1.00      | ~ r1_orders_2(X0,X3,X2)
% 2.97/1.00      | r1_orders_2(X0,X1,sK0(X0,X3,X1,X2))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.97/1.00      | ~ v5_orders_2(X0)
% 2.97/1.00      | ~ l1_orders_2(X0)
% 2.97/1.00      | k10_lattice3(X0,X3,X1) = X2
% 2.97/1.00      | sK2 != X0 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_248,c_28]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_535,plain,
% 2.97/1.00      ( ~ r1_orders_2(sK2,X0,X1)
% 2.97/1.00      | ~ r1_orders_2(sK2,X2,X1)
% 2.97/1.00      | r1_orders_2(sK2,X0,sK0(sK2,X2,X0,X1))
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 2.97/1.00      | ~ v5_orders_2(sK2)
% 2.97/1.00      | ~ l1_orders_2(sK2)
% 2.97/1.00      | k10_lattice3(sK2,X2,X0) = X1 ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_534]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_539,plain,
% 2.97/1.00      ( ~ r1_orders_2(sK2,X0,X1)
% 2.97/1.00      | ~ r1_orders_2(sK2,X2,X1)
% 2.97/1.00      | r1_orders_2(sK2,X0,sK0(sK2,X2,X0,X1))
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 2.97/1.00      | k10_lattice3(sK2,X2,X0) = X1 ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_535,c_29,c_26]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_540,plain,
% 2.97/1.00      ( ~ r1_orders_2(sK2,X0,X1)
% 2.97/1.00      | ~ r1_orders_2(sK2,X2,X1)
% 2.97/1.00      | r1_orders_2(sK2,X0,sK0(sK2,X2,X0,X1))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | k10_lattice3(sK2,X2,X0) = X1 ),
% 2.97/1.00      inference(renaming,[status(thm)],[c_539]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1269,plain,
% 2.97/1.00      ( ~ r1_orders_2(sK2,X0_48,X1_48)
% 2.97/1.00      | ~ r1_orders_2(sK2,X2_48,X1_48)
% 2.97/1.00      | r1_orders_2(sK2,X0_48,sK0(sK2,X2_48,X0_48,X1_48))
% 2.97/1.00      | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X2_48,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
% 2.97/1.00      | k10_lattice3(sK2,X2_48,X0_48) = X1_48 ),
% 2.97/1.00      inference(subtyping,[status(esa)],[c_540]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2114,plain,
% 2.97/1.00      ( ~ r1_orders_2(sK2,k12_lattice3(sK2,sK3,sK4),X0_48)
% 2.97/1.00      | ~ r1_orders_2(sK2,sK4,X0_48)
% 2.97/1.00      | r1_orders_2(sK2,sK4,sK0(sK2,k12_lattice3(sK2,sK3,sK4),sK4,X0_48))
% 2.97/1.00      | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 2.97/1.00      | k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = X0_48 ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_1269]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2125,plain,
% 2.97/1.00      ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = X0_48
% 2.97/1.00      | r1_orders_2(sK2,k12_lattice3(sK2,sK3,sK4),X0_48) != iProver_top
% 2.97/1.00      | r1_orders_2(sK2,sK4,X0_48) != iProver_top
% 2.97/1.00      | r1_orders_2(sK2,sK4,sK0(sK2,k12_lattice3(sK2,sK3,sK4),sK4,X0_48)) = iProver_top
% 2.97/1.00      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
% 2.97/1.00      | m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 2.97/1.00      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_2114]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2127,plain,
% 2.97/1.00      ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = sK4
% 2.97/1.00      | r1_orders_2(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != iProver_top
% 2.97/1.00      | r1_orders_2(sK2,sK4,sK0(sK2,k12_lattice3(sK2,sK3,sK4),sK4,sK4)) = iProver_top
% 2.97/1.00      | r1_orders_2(sK2,sK4,sK4) != iProver_top
% 2.97/1.00      | m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 2.97/1.00      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_2125]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1280,plain,
% 2.97/1.00      ( X0_48 != X1_48 | X2_48 != X1_48 | X2_48 = X0_48 ),
% 2.97/1.00      theory(equality) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2030,plain,
% 2.97/1.00      ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != X0_48
% 2.97/1.00      | sK4 != X0_48
% 2.97/1.00      | sK4 = k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_1280]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2031,plain,
% 2.97/1.00      ( k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != sK4
% 2.97/1.00      | sK4 = k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4)
% 2.97/1.00      | sK4 != sK4 ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_2030]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_22,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.97/1.00      | ~ v5_orders_2(X1)
% 2.97/1.00      | ~ v1_lattice3(X1)
% 2.97/1.00      | ~ l1_orders_2(X1)
% 2.97/1.00      | k13_lattice3(X1,X2,X0) = k10_lattice3(X1,X2,X0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_706,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.97/1.00      | ~ v5_orders_2(X1)
% 2.97/1.00      | ~ l1_orders_2(X1)
% 2.97/1.00      | k13_lattice3(X1,X2,X0) = k10_lattice3(X1,X2,X0)
% 2.97/1.00      | sK2 != X1 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_28]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_707,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | ~ v5_orders_2(sK2)
% 2.97/1.00      | ~ l1_orders_2(sK2)
% 2.97/1.00      | k13_lattice3(sK2,X0,X1) = k10_lattice3(sK2,X0,X1) ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_706]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_711,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | k13_lattice3(sK2,X0,X1) = k10_lattice3(sK2,X0,X1) ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_707,c_29,c_26]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_712,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | k13_lattice3(sK2,X1,X0) = k10_lattice3(sK2,X1,X0) ),
% 2.97/1.00      inference(renaming,[status(thm)],[c_711]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1263,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0_48,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
% 2.97/1.00      | k13_lattice3(sK2,X1_48,X0_48) = k10_lattice3(sK2,X1_48,X0_48) ),
% 2.97/1.00      inference(subtyping,[status(esa)],[c_712]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1984,plain,
% 2.97/1.00      ( ~ m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 2.97/1.00      | k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_1263]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1985,plain,
% 2.97/1.00      ( k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4)
% 2.97/1.00      | m1_subset_1(k12_lattice3(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 2.97/1.00      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_1984]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1973,plain,
% 2.97/1.00      ( k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != X0_48
% 2.97/1.00      | k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = sK4
% 2.97/1.00      | sK4 != X0_48 ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_1280]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1983,plain,
% 2.97/1.00      ( k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4)
% 2.97/1.00      | k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) = sK4
% 2.97/1.00      | sK4 != k10_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_1973]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2,plain,
% 2.97/1.00      ( r3_orders_2(X0,X1,X1)
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | v2_struct_0(X0)
% 2.97/1.00      | ~ v3_orders_2(X0)
% 2.97/1.00      | ~ l1_orders_2(X0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_30,negated_conjecture,
% 2.97/1.00      ( v3_orders_2(sK2) ),
% 2.97/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_398,plain,
% 2.97/1.00      ( r3_orders_2(X0,X1,X1)
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | v2_struct_0(X0)
% 2.97/1.00      | ~ l1_orders_2(X0)
% 2.97/1.00      | sK2 != X0 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_30]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_399,plain,
% 2.97/1.00      ( r3_orders_2(sK2,X0,X0)
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | v2_struct_0(sK2)
% 2.97/1.00      | ~ l1_orders_2(sK2) ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_398]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_85,plain,
% 2.97/1.00      ( ~ v2_lattice3(sK2) | ~ v2_struct_0(sK2) | ~ l1_orders_2(sK2) ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_403,plain,
% 2.97/1.00      ( r3_orders_2(sK2,X0,X0)
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_399,c_27,c_26,c_85]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_404,plain,
% 2.97/1.00      ( r3_orders_2(sK2,X0,X0)
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 2.97/1.00      inference(renaming,[status(thm)],[c_403]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1,plain,
% 2.97/1.00      ( r1_orders_2(X0,X1,X2)
% 2.97/1.00      | ~ r3_orders_2(X0,X1,X2)
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | v2_struct_0(X0)
% 2.97/1.00      | ~ v3_orders_2(X0)
% 2.97/1.00      | ~ l1_orders_2(X0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_419,plain,
% 2.97/1.00      ( r1_orders_2(X0,X1,X2)
% 2.97/1.00      | ~ r3_orders_2(X0,X1,X2)
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | v2_struct_0(X0)
% 2.97/1.00      | ~ l1_orders_2(X0)
% 2.97/1.00      | sK2 != X0 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_30]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_420,plain,
% 2.97/1.00      ( r1_orders_2(sK2,X0,X1)
% 2.97/1.00      | ~ r3_orders_2(sK2,X0,X1)
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | v2_struct_0(sK2)
% 2.97/1.00      | ~ l1_orders_2(sK2) ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_419]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_424,plain,
% 2.97/1.00      ( r1_orders_2(sK2,X0,X1)
% 2.97/1.00      | ~ r3_orders_2(sK2,X0,X1)
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_420,c_27,c_26,c_85]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_425,plain,
% 2.97/1.00      ( r1_orders_2(sK2,X0,X1)
% 2.97/1.00      | ~ r3_orders_2(sK2,X0,X1)
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 2.97/1.00      inference(renaming,[status(thm)],[c_424]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_482,plain,
% 2.97/1.00      ( r1_orders_2(sK2,X0,X1)
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | X0 != X3
% 2.97/1.00      | X1 != X3
% 2.97/1.00      | sK2 != sK2 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_404,c_425]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_483,plain,
% 2.97/1.00      ( r1_orders_2(sK2,X0,X0)
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_482]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1271,plain,
% 2.97/1.00      ( r1_orders_2(sK2,X0_48,X0_48)
% 2.97/1.00      | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
% 2.97/1.00      | ~ m1_subset_1(X0_48,u1_struct_0(sK2)) ),
% 2.97/1.00      inference(subtyping,[status(esa)],[c_483]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1275,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0_48,u1_struct_0(sK2)) | ~ sP0_iProver_split ),
% 2.97/1.00      inference(splitting,
% 2.97/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.97/1.00                [c_1271]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1297,plain,
% 2.97/1.00      ( m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
% 2.97/1.00      | sP0_iProver_split != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_1275]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1299,plain,
% 2.97/1.00      ( m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 2.97/1.00      | sP0_iProver_split != iProver_top ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_1297]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1276,plain,
% 2.97/1.00      ( r1_orders_2(sK2,X0_48,X0_48)
% 2.97/1.00      | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
% 2.97/1.00      | ~ sP1_iProver_split ),
% 2.97/1.00      inference(splitting,
% 2.97/1.00                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.97/1.00                [c_1271]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1294,plain,
% 2.97/1.00      ( r1_orders_2(sK2,X0_48,X0_48) = iProver_top
% 2.97/1.00      | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
% 2.97/1.00      | sP1_iProver_split != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_1276]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1296,plain,
% 2.97/1.00      ( r1_orders_2(sK2,sK4,sK4) = iProver_top
% 2.97/1.00      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 2.97/1.00      | sP1_iProver_split != iProver_top ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_1294]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1277,plain,
% 2.97/1.00      ( sP1_iProver_split | sP0_iProver_split ),
% 2.97/1.00      inference(splitting,
% 2.97/1.00                [splitting(split),new_symbols(definition,[])],
% 2.97/1.00                [c_1271]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1293,plain,
% 2.97/1.00      ( sP1_iProver_split = iProver_top
% 2.97/1.00      | sP0_iProver_split = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_1277]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_23,negated_conjecture,
% 2.97/1.00      ( k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != sK4 ),
% 2.97/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1274,negated_conjecture,
% 2.97/1.00      ( k13_lattice3(sK2,k12_lattice3(sK2,sK3,sK4),sK4) != sK4 ),
% 2.97/1.00      inference(subtyping,[status(esa)],[c_23]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1279,plain,( X0_48 = X0_48 ),theory(equality) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1290,plain,
% 2.97/1.00      ( sK4 = sK4 ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_1279]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_37,plain,
% 2.97/1.00      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_36,plain,
% 2.97/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(contradiction,plain,
% 2.97/1.00      ( $false ),
% 2.97/1.00      inference(minisat,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_4867,c_2920,c_2131,c_2127,c_2031,c_1985,c_1983,c_1299,
% 2.97/1.00                 c_1296,c_1293,c_1274,c_1290,c_37,c_36]) ).
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
% 2.97/1.00  parsing_time:                           0.013
% 2.97/1.00  unif_index_cands_time:                  0.
% 2.97/1.00  unif_index_add_time:                    0.
% 2.97/1.00  orderings_time:                         0.
% 2.97/1.00  out_proof_time:                         0.012
% 2.97/1.00  total_time:                             0.181
% 2.97/1.00  num_of_symbols:                         52
% 2.97/1.00  num_of_terms:                           4765
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
% 2.97/1.00  res_preprocessed:                       112
% 2.97/1.00  prep_upred:                             0
% 2.97/1.00  prep_unflattend:                        23
% 2.97/1.00  smt_new_axioms:                         0
% 2.97/1.00  pred_elim_cands:                        2
% 2.97/1.00  pred_elim:                              7
% 2.97/1.00  pred_elim_cl:                           9
% 2.97/1.00  pred_elim_cycles:                       9
% 2.97/1.00  merged_defs:                            0
% 2.97/1.00  merged_defs_ncl:                        0
% 2.97/1.00  bin_hyper_res:                          0
% 2.97/1.00  prep_cycles:                            4
% 2.97/1.00  pred_elim_time:                         0.015
% 2.97/1.00  splitting_time:                         0.
% 2.97/1.00  sem_filter_time:                        0.
% 2.97/1.00  monotx_time:                            0.
% 2.97/1.00  subtype_inf_time:                       0.
% 2.97/1.00  
% 2.97/1.00  ------ Problem properties
% 2.97/1.00  
% 2.97/1.00  clauses:                                24
% 2.97/1.00  conjectures:                            3
% 2.97/1.00  epr:                                    1
% 2.97/1.00  horn:                                   17
% 2.97/1.00  ground:                                 4
% 2.97/1.00  unary:                                  3
% 2.97/1.00  binary:                                 2
% 2.97/1.00  lits:                                   105
% 2.97/1.00  lits_eq:                                12
% 2.97/1.00  fd_pure:                                0
% 2.97/1.00  fd_pseudo:                              0
% 2.97/1.00  fd_cond:                                0
% 2.97/1.00  fd_pseudo_cond:                         8
% 2.97/1.00  ac_symbols:                             0
% 2.97/1.00  
% 2.97/1.00  ------ Propositional Solver
% 2.97/1.00  
% 2.97/1.00  prop_solver_calls:                      28
% 2.97/1.00  prop_fast_solver_calls:                 1585
% 2.97/1.00  smt_solver_calls:                       0
% 2.97/1.00  smt_fast_solver_calls:                  0
% 2.97/1.00  prop_num_of_clauses:                    1534
% 2.97/1.00  prop_preprocess_simplified:             4754
% 2.97/1.00  prop_fo_subsumed:                       61
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
% 2.97/1.00  inst_num_of_clauses:                    405
% 2.97/1.00  inst_num_in_passive:                    34
% 2.97/1.00  inst_num_in_active:                     204
% 2.97/1.00  inst_num_in_unprocessed:                167
% 2.97/1.00  inst_num_of_loops:                      240
% 2.97/1.00  inst_num_of_learning_restarts:          0
% 2.97/1.00  inst_num_moves_active_passive:          32
% 2.97/1.00  inst_lit_activity:                      0
% 2.97/1.00  inst_lit_activity_moves:                0
% 2.97/1.00  inst_num_tautologies:                   0
% 2.97/1.00  inst_num_prop_implied:                  0
% 2.97/1.00  inst_num_existing_simplified:           0
% 2.97/1.00  inst_num_eq_res_simplified:             0
% 2.97/1.00  inst_num_child_elim:                    0
% 2.97/1.00  inst_num_of_dismatching_blockings:      83
% 2.97/1.00  inst_num_of_non_proper_insts:           362
% 2.97/1.00  inst_num_of_duplicates:                 0
% 2.97/1.00  inst_inst_num_from_inst_to_res:         0
% 2.97/1.00  inst_dismatching_checking_time:         0.
% 2.97/1.00  
% 2.97/1.00  ------ Resolution
% 2.97/1.00  
% 2.97/1.00  res_num_of_clauses:                     0
% 2.97/1.00  res_num_in_passive:                     0
% 2.97/1.00  res_num_in_active:                      0
% 2.97/1.00  res_num_of_loops:                       116
% 2.97/1.00  res_forward_subset_subsumed:            30
% 2.97/1.00  res_backward_subset_subsumed:           0
% 2.97/1.00  res_forward_subsumed:                   0
% 2.97/1.00  res_backward_subsumed:                  0
% 2.97/1.00  res_forward_subsumption_resolution:     0
% 2.97/1.00  res_backward_subsumption_resolution:    3
% 2.97/1.00  res_clause_to_clause_subsumption:       439
% 2.97/1.00  res_orphan_elimination:                 0
% 2.97/1.00  res_tautology_del:                      35
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
% 2.97/1.00  sup_num_of_clauses:                     103
% 2.97/1.00  sup_num_in_active:                      47
% 2.97/1.00  sup_num_in_passive:                     56
% 2.97/1.00  sup_num_of_loops:                       47
% 2.97/1.00  sup_fw_superposition:                   30
% 2.97/1.00  sup_bw_superposition:                   56
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
% 2.97/1.00  sim_eq_tautology_del:                   2
% 2.97/1.00  sim_eq_res_simp:                        0
% 2.97/1.00  sim_fw_demodulated:                     0
% 2.97/1.00  sim_bw_demodulated:                     1
% 2.97/1.00  sim_light_normalised:                   0
% 2.97/1.00  sim_joinable_taut:                      0
% 2.97/1.00  sim_joinable_simp:                      0
% 2.97/1.00  sim_ac_normalised:                      0
% 2.97/1.00  sim_smt_subsumption:                    0
% 2.97/1.00  
%------------------------------------------------------------------------------
