%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:04 EST 2020

% Result     : Theorem 19.60s
% Output     : CNFRefutation 19.60s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 303 expanded)
%              Number of clauses        :   70 (  96 expanded)
%              Number of leaves         :   19 (  85 expanded)
%              Depth                    :   20
%              Number of atoms          :  933 (2185 expanded)
%              Number of equality atoms :   96 ( 283 expanded)
%              Maximal formula depth    :   17 (   8 average)
%              Maximal clause size      :   21 (   6 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

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

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f74,plain,(
    k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
    inference(cnf_transformation,[],[f45])).

fof(f67,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f68,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,(
    v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f70,plain,(
    v2_lattice3(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f72,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f45])).

fof(f73,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(cnf_transformation,[],[f63])).

cnf(c_1,plain,
    ( ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_313,plain,
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

cnf(c_314,plain,
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
    inference(renaming,[status(thm)],[c_313])).

cnf(c_451,plain,
    ( ~ r1_orders_2(X0_46,X0_47,X1_47)
    | ~ r1_orders_2(X0_46,X0_47,X2_47)
    | ~ r1_orders_2(X0_46,sK1(X0_46,X1_47,X2_47,X0_47),X0_47)
    | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
    | ~ m1_subset_1(X2_47,u1_struct_0(X0_46))
    | ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
    | ~ v5_orders_2(X0_46)
    | ~ v2_lattice3(X0_46)
    | ~ l1_orders_2(X0_46)
    | k11_lattice3(X0_46,X1_47,X2_47) = X0_47 ),
    inference(subtyping,[status(esa)],[c_314])).

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
    inference(cnf_transformation,[],[f61])).

cnf(c_279,plain,
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

cnf(c_280,plain,
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
    inference(renaming,[status(thm)],[c_279])).

cnf(c_455,plain,
    ( ~ r1_orders_2(X0_46,X0_47,X1_47)
    | ~ r1_orders_2(X0_46,X0_47,X2_47)
    | r1_orders_2(X0_46,sK1(X0_46,X1_47,X2_47,X0_47),X1_47)
    | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
    | ~ m1_subset_1(X2_47,u1_struct_0(X0_46))
    | ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
    | ~ v5_orders_2(X0_46)
    | ~ v2_lattice3(X0_46)
    | ~ l1_orders_2(X0_46)
    | k11_lattice3(X0_46,X1_47,X2_47) = X0_47 ),
    inference(subtyping,[status(esa)],[c_280])).

cnf(c_39039,plain,
    ( ~ r1_orders_2(X0_46,X0_47,X1_47)
    | ~ r1_orders_2(X0_46,X0_47,X0_47)
    | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
    | ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
    | ~ v5_orders_2(X0_46)
    | ~ v2_lattice3(X0_46)
    | ~ l1_orders_2(X0_46)
    | k11_lattice3(X0_46,X0_47,X1_47) = X0_47 ),
    inference(resolution,[status(thm)],[c_451,c_455])).

cnf(c_480,plain,
    ( X0_47 != X1_47
    | X2_47 != X1_47
    | X2_47 = X0_47 ),
    theory(equality)).

cnf(c_479,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_1425,plain,
    ( X0_47 != X1_47
    | X1_47 = X0_47 ),
    inference(resolution,[status(thm)],[c_480,c_479])).

cnf(c_43916,plain,
    ( ~ r1_orders_2(X0_46,X0_47,X1_47)
    | ~ r1_orders_2(X0_46,X0_47,X0_47)
    | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
    | ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
    | ~ v5_orders_2(X0_46)
    | ~ v2_lattice3(X0_46)
    | ~ l1_orders_2(X0_46)
    | X0_47 = k11_lattice3(X0_46,X0_47,X1_47) ),
    inference(resolution,[status(thm)],[c_39039,c_1425])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_475,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
    | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
    | ~ v5_orders_2(X0_46)
    | ~ v2_lattice3(X0_46)
    | ~ l1_orders_2(X0_46)
    | k11_lattice3(X0_46,X0_47,X1_47) = k12_lattice3(X0_46,X0_47,X1_47) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_4030,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
    | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
    | ~ v5_orders_2(X0_46)
    | ~ v2_lattice3(X0_46)
    | ~ l1_orders_2(X0_46)
    | k12_lattice3(X0_46,X1_47,X0_47) = k11_lattice3(X0_46,X1_47,X0_47) ),
    inference(resolution,[status(thm)],[c_475,c_1425])).

cnf(c_4692,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
    | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
    | ~ v5_orders_2(X0_46)
    | ~ v2_lattice3(X0_46)
    | ~ l1_orders_2(X0_46)
    | X2_47 != k11_lattice3(X0_46,X0_47,X1_47)
    | k12_lattice3(X0_46,X0_47,X1_47) = X2_47 ),
    inference(resolution,[status(thm)],[c_4030,c_480])).

cnf(c_45595,plain,
    ( ~ r1_orders_2(X0_46,X0_47,X1_47)
    | ~ r1_orders_2(X0_46,X0_47,X0_47)
    | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
    | ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
    | ~ v5_orders_2(X0_46)
    | ~ v2_lattice3(X0_46)
    | ~ l1_orders_2(X0_46)
    | k12_lattice3(X0_46,X0_47,X1_47) = X0_47 ),
    inference(resolution,[status(thm)],[c_43916,c_4692])).

cnf(c_21,negated_conjecture,
    ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_472,negated_conjecture,
    ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_46334,plain,
    ( ~ r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
    | ~ r1_orders_2(sK2,sK3,sK3)
    | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ v2_lattice3(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(resolution,[status(thm)],[c_45595,c_472])).

cnf(c_28,negated_conjecture,
    ( v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_27,negated_conjecture,
    ( v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_26,negated_conjecture,
    ( v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_25,negated_conjecture,
    ( v2_lattice3(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_24,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_490,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_479])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k12_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_476,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
    | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
    | m1_subset_1(k12_lattice3(X0_46,X0_47,X1_47),u1_struct_0(X0_46))
    | ~ v5_orders_2(X0_46)
    | ~ v2_lattice3(X0_46)
    | ~ l1_orders_2(X0_46) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_495,plain,
    ( m1_subset_1(k12_lattice3(sK2,sK3,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ v2_lattice3(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(instantiation,[status(thm)],[c_476])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | k13_lattice3(X1,X2,X0) = k10_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_474,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
    | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
    | ~ v5_orders_2(X0_46)
    | ~ l1_orders_2(X0_46)
    | ~ v1_lattice3(X0_46)
    | k13_lattice3(X0_46,X0_47,X1_47) = k10_lattice3(X0_46,X0_47,X1_47) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1542,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | ~ v1_lattice3(sK2)
    | k13_lattice3(sK2,sK3,sK4) = k10_lattice3(sK2,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_474])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k10_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_477,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
    | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
    | m1_subset_1(k10_lattice3(X0_46,X0_47,X1_47),u1_struct_0(X0_46))
    | ~ l1_orders_2(X0_46) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_7503,plain,
    ( m1_subset_1(k10_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(instantiation,[status(thm)],[c_477])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | k13_lattice3(X1,k12_lattice3(X1,X2,X0),X0) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_473,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
    | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
    | ~ v3_orders_2(X0_46)
    | ~ v5_orders_2(X0_46)
    | ~ v2_lattice3(X0_46)
    | ~ l1_orders_2(X0_46)
    | ~ v1_lattice3(X0_46)
    | k13_lattice3(X0_46,k12_lattice3(X0_46,X0_47,X1_47),X1_47) = X1_47 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_4291,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
    | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
    | ~ v3_orders_2(X0_46)
    | ~ v5_orders_2(X0_46)
    | ~ v2_lattice3(X0_46)
    | ~ l1_orders_2(X0_46)
    | ~ v1_lattice3(X0_46)
    | X0_47 = k13_lattice3(X0_46,k12_lattice3(X0_46,X1_47,X0_47),X0_47) ),
    inference(resolution,[status(thm)],[c_473,c_1425])).

cnf(c_483,plain,
    ( ~ r1_orders_2(X0_46,X0_47,X1_47)
    | r1_orders_2(X0_46,X2_47,X3_47)
    | X2_47 != X0_47
    | X3_47 != X1_47 ),
    theory(equality)).

cnf(c_8010,plain,
    ( r1_orders_2(X0_46,X0_47,X1_47)
    | ~ r1_orders_2(X0_46,X2_47,k13_lattice3(X1_46,k12_lattice3(X1_46,X3_47,X1_47),X1_47))
    | ~ m1_subset_1(X1_47,u1_struct_0(X1_46))
    | ~ m1_subset_1(X3_47,u1_struct_0(X1_46))
    | ~ v3_orders_2(X1_46)
    | ~ v5_orders_2(X1_46)
    | ~ v2_lattice3(X1_46)
    | ~ l1_orders_2(X1_46)
    | ~ v1_lattice3(X1_46)
    | X0_47 != X2_47 ),
    inference(resolution,[status(thm)],[c_4291,c_483])).

cnf(c_3603,plain,
    ( r1_orders_2(X0_46,X0_47,k13_lattice3(X1_46,X1_47,X2_47))
    | ~ r1_orders_2(X0_46,X3_47,k10_lattice3(X1_46,X1_47,X2_47))
    | ~ m1_subset_1(X2_47,u1_struct_0(X1_46))
    | ~ m1_subset_1(X1_47,u1_struct_0(X1_46))
    | ~ v5_orders_2(X1_46)
    | ~ l1_orders_2(X1_46)
    | ~ v1_lattice3(X1_46)
    | X0_47 != X3_47 ),
    inference(resolution,[status(thm)],[c_474,c_483])).

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

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_204,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_0])).

cnf(c_205,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0) ),
    inference(renaming,[status(thm)],[c_204])).

cnf(c_464,plain,
    ( r1_orders_2(X0_46,X0_47,k10_lattice3(X0_46,X1_47,X0_47))
    | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
    | ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
    | ~ m1_subset_1(k10_lattice3(X0_46,X1_47,X0_47),u1_struct_0(X0_46))
    | ~ v5_orders_2(X0_46)
    | ~ l1_orders_2(X0_46)
    | ~ v1_lattice3(X0_46) ),
    inference(subtyping,[status(esa)],[c_205])).

cnf(c_1526,plain,
    ( r1_orders_2(X0_46,X0_47,k10_lattice3(X0_46,X1_47,X0_47))
    | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
    | ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
    | ~ v5_orders_2(X0_46)
    | ~ l1_orders_2(X0_46)
    | ~ v1_lattice3(X0_46) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_477,c_464])).

cnf(c_9481,plain,
    ( r1_orders_2(X0_46,X0_47,k13_lattice3(X0_46,X1_47,X2_47))
    | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
    | ~ m1_subset_1(X2_47,u1_struct_0(X0_46))
    | ~ v5_orders_2(X0_46)
    | ~ l1_orders_2(X0_46)
    | ~ v1_lattice3(X0_46)
    | X0_47 != X2_47 ),
    inference(resolution,[status(thm)],[c_3603,c_1526])).

cnf(c_28666,plain,
    ( r1_orders_2(X0_46,X0_47,X1_47)
    | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
    | ~ m1_subset_1(X2_47,u1_struct_0(X0_46))
    | ~ m1_subset_1(k12_lattice3(X0_46,X2_47,X1_47),u1_struct_0(X0_46))
    | ~ v3_orders_2(X0_46)
    | ~ v5_orders_2(X0_46)
    | ~ v2_lattice3(X0_46)
    | ~ l1_orders_2(X0_46)
    | ~ v1_lattice3(X0_46)
    | X3_47 != X1_47
    | X0_47 != X3_47 ),
    inference(resolution,[status(thm)],[c_8010,c_9481])).

cnf(c_28668,plain,
    ( r1_orders_2(sK2,sK3,sK3)
    | ~ m1_subset_1(k12_lattice3(sK2,sK3,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ v3_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v2_lattice3(sK2)
    | ~ l1_orders_2(sK2)
    | ~ v1_lattice3(sK2)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_28666])).

cnf(c_481,plain,
    ( ~ m1_subset_1(X0_47,X0_48)
    | m1_subset_1(X1_47,X0_48)
    | X1_47 != X0_47 ),
    theory(equality)).

cnf(c_1338,plain,
    ( m1_subset_1(X0_47,u1_struct_0(X0_46))
    | ~ m1_subset_1(k10_lattice3(X0_46,X1_47,X2_47),u1_struct_0(X0_46))
    | X0_47 != k10_lattice3(X0_46,X1_47,X2_47) ),
    inference(instantiation,[status(thm)],[c_481])).

cnf(c_3634,plain,
    ( m1_subset_1(k13_lattice3(sK2,X0_47,X1_47),u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X2_47,X3_47),u1_struct_0(sK2))
    | k13_lattice3(sK2,X0_47,X1_47) != k10_lattice3(sK2,X2_47,X3_47) ),
    inference(instantiation,[status(thm)],[c_1338])).

cnf(c_8109,plain,
    ( m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X0_47,X1_47),u1_struct_0(sK2))
    | k13_lattice3(sK2,sK3,sK4) != k10_lattice3(sK2,X0_47,X1_47) ),
    inference(instantiation,[status(thm)],[c_3634])).

cnf(c_32071,plain,
    ( m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | k13_lattice3(sK2,sK3,sK4) != k10_lattice3(sK2,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_8109])).

cnf(c_46989,plain,
    ( ~ r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_46334,c_28,c_27,c_26,c_25,c_24,c_23,c_22,c_490,c_495,c_1542,c_7503,c_28668,c_32071])).

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

cnf(c_213,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_0])).

cnf(c_214,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0) ),
    inference(renaming,[status(thm)],[c_213])).

cnf(c_463,plain,
    ( r1_orders_2(X0_46,X0_47,k10_lattice3(X0_46,X0_47,X1_47))
    | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
    | ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
    | ~ m1_subset_1(k10_lattice3(X0_46,X0_47,X1_47),u1_struct_0(X0_46))
    | ~ v5_orders_2(X0_46)
    | ~ l1_orders_2(X0_46)
    | ~ v1_lattice3(X0_46) ),
    inference(subtyping,[status(esa)],[c_214])).

cnf(c_634,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
    | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
    | r1_orders_2(X0_46,X0_47,k10_lattice3(X0_46,X0_47,X1_47))
    | ~ v5_orders_2(X0_46)
    | ~ l1_orders_2(X0_46)
    | ~ v1_lattice3(X0_46) ),
    inference(global_propositional_subsumption,[status(thm)],[c_463,c_477])).

cnf(c_635,plain,
    ( r1_orders_2(X0_46,X0_47,k10_lattice3(X0_46,X0_47,X1_47))
    | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
    | ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
    | ~ v5_orders_2(X0_46)
    | ~ l1_orders_2(X0_46)
    | ~ v1_lattice3(X0_46) ),
    inference(renaming,[status(thm)],[c_634])).

cnf(c_9477,plain,
    ( r1_orders_2(X0_46,X0_47,k13_lattice3(X0_46,X1_47,X2_47))
    | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
    | ~ m1_subset_1(X2_47,u1_struct_0(X0_46))
    | ~ v5_orders_2(X0_46)
    | ~ l1_orders_2(X0_46)
    | ~ v1_lattice3(X0_46)
    | X0_47 != X1_47 ),
    inference(resolution,[status(thm)],[c_3603,c_635])).

cnf(c_47001,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | ~ v1_lattice3(sK2)
    | sK3 != sK3 ),
    inference(resolution,[status(thm)],[c_46989,c_9477])).

cnf(c_47004,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | ~ v1_lattice3(sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_47001])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_47004,c_22,c_23,c_24,c_26,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:53:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 19.60/2.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.60/2.99  
% 19.60/2.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.60/2.99  
% 19.60/2.99  ------  iProver source info
% 19.60/2.99  
% 19.60/2.99  git: date: 2020-06-30 10:37:57 +0100
% 19.60/2.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.60/2.99  git: non_committed_changes: false
% 19.60/2.99  git: last_make_outside_of_git: false
% 19.60/2.99  
% 19.60/2.99  ------ 
% 19.60/2.99  ------ Parsing...
% 19.60/2.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.60/2.99  
% 19.60/2.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 19.60/2.99  
% 19.60/2.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.60/2.99  
% 19.60/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.60/2.99  ------ Proving...
% 19.60/2.99  ------ Problem Properties 
% 19.60/2.99  
% 19.60/2.99  
% 19.60/2.99  clauses                                 27
% 19.60/2.99  conjectures                             8
% 19.60/2.99  EPR                                     5
% 19.60/2.99  Horn                                    21
% 19.60/2.99  unary                                   8
% 19.60/2.99  binary                                  0
% 19.60/2.99  lits                                    166
% 19.60/2.99  lits eq                                 12
% 19.60/2.99  fd_pure                                 0
% 19.60/2.99  fd_pseudo                               0
% 19.60/2.99  fd_cond                                 0
% 19.60/2.99  fd_pseudo_cond                          8
% 19.60/2.99  AC symbols                              0
% 19.60/2.99  
% 19.60/2.99  ------ Input Options Time Limit: Unbounded
% 19.60/2.99  
% 19.60/2.99  
% 19.60/2.99  ------ 
% 19.60/2.99  Current options:
% 19.60/2.99  ------ 
% 19.60/2.99  
% 19.60/2.99  
% 19.60/2.99  
% 19.60/2.99  
% 19.60/2.99  ------ Proving...
% 19.60/2.99  
% 19.60/2.99  
% 19.60/2.99  % SZS status Theorem for theBenchmark.p
% 19.60/2.99  
% 19.60/2.99  % SZS output start CNFRefutation for theBenchmark.p
% 19.60/2.99  
% 19.60/2.99  fof(f6,axiom,(
% 19.60/2.99    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 19.60/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.60/2.99  
% 19.60/2.99  fof(f22,plain,(
% 19.60/2.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 19.60/2.99    inference(ennf_transformation,[],[f6])).
% 19.60/2.99  
% 19.60/2.99  fof(f23,plain,(
% 19.60/2.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 19.60/2.99    inference(flattening,[],[f22])).
% 19.60/2.99  
% 19.60/2.99  fof(f37,plain,(
% 19.60/2.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 19.60/2.99    inference(nnf_transformation,[],[f23])).
% 19.60/2.99  
% 19.60/2.99  fof(f38,plain,(
% 19.60/2.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 19.60/2.99    inference(flattening,[],[f37])).
% 19.60/2.99  
% 19.60/2.99  fof(f39,plain,(
% 19.60/2.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 19.60/2.99    inference(rectify,[],[f38])).
% 19.60/2.99  
% 19.60/2.99  fof(f40,plain,(
% 19.60/2.99    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK1(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X1) & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0))))),
% 19.60/2.99    introduced(choice_axiom,[])).
% 19.60/2.99  
% 19.60/2.99  fof(f41,plain,(
% 19.60/2.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,sK1(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X1) & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 19.60/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).
% 19.60/2.99  
% 19.60/2.99  fof(f63,plain,(
% 19.60/2.99    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,sK1(X0,X1,X2,X3),X3) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 19.60/2.99    inference(cnf_transformation,[],[f41])).
% 19.60/2.99  
% 19.60/2.99  fof(f2,axiom,(
% 19.60/2.99    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 19.60/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.60/2.99  
% 19.60/2.99  fof(f14,plain,(
% 19.60/2.99    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 19.60/2.99    inference(ennf_transformation,[],[f2])).
% 19.60/2.99  
% 19.60/2.99  fof(f15,plain,(
% 19.60/2.99    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 19.60/2.99    inference(flattening,[],[f14])).
% 19.60/2.99  
% 19.60/2.99  fof(f47,plain,(
% 19.60/2.99    ( ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0)) )),
% 19.60/2.99    inference(cnf_transformation,[],[f15])).
% 19.60/2.99  
% 19.60/2.99  fof(f61,plain,(
% 19.60/2.99    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | r1_orders_2(X0,sK1(X0,X1,X2,X3),X1) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 19.60/2.99    inference(cnf_transformation,[],[f41])).
% 19.60/2.99  
% 19.60/2.99  fof(f7,axiom,(
% 19.60/2.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2))),
% 19.60/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.60/2.99  
% 19.60/2.99  fof(f24,plain,(
% 19.60/2.99    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 19.60/2.99    inference(ennf_transformation,[],[f7])).
% 19.60/2.99  
% 19.60/2.99  fof(f25,plain,(
% 19.60/2.99    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 19.60/2.99    inference(flattening,[],[f24])).
% 19.60/2.99  
% 19.60/2.99  fof(f64,plain,(
% 19.60/2.99    ( ! [X2,X0,X1] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 19.60/2.99    inference(cnf_transformation,[],[f25])).
% 19.60/2.99  
% 19.60/2.99  fof(f10,conjecture,(
% 19.60/2.99    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1)))),
% 19.60/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.60/2.99  
% 19.60/2.99  fof(f11,negated_conjecture,(
% 19.60/2.99    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1)))),
% 19.60/2.99    inference(negated_conjecture,[],[f10])).
% 19.60/2.99  
% 19.60/2.99  fof(f30,plain,(
% 19.60/2.99    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)))),
% 19.60/2.99    inference(ennf_transformation,[],[f11])).
% 19.60/2.99  
% 19.60/2.99  fof(f31,plain,(
% 19.60/2.99    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 19.60/2.99    inference(flattening,[],[f30])).
% 19.60/2.99  
% 19.60/2.99  fof(f44,plain,(
% 19.60/2.99    ( ! [X0,X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) => (k12_lattice3(X0,X1,k13_lattice3(X0,X1,sK4)) != X1 & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 19.60/2.99    introduced(choice_axiom,[])).
% 19.60/2.99  
% 19.60/2.99  fof(f43,plain,(
% 19.60/2.99    ( ! [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k12_lattice3(X0,sK3,k13_lattice3(X0,sK3,X2)) != sK3 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 19.60/2.99    introduced(choice_axiom,[])).
% 19.60/2.99  
% 19.60/2.99  fof(f42,plain,(
% 19.60/2.99    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => (? [X1] : (? [X2] : (k12_lattice3(sK2,X1,k13_lattice3(sK2,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_orders_2(sK2) & v2_lattice3(sK2) & v1_lattice3(sK2) & v5_orders_2(sK2) & v3_orders_2(sK2))),
% 19.60/2.99    introduced(choice_axiom,[])).
% 19.60/2.99  
% 19.60/2.99  fof(f45,plain,(
% 19.60/2.99    ((k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 & m1_subset_1(sK4,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_orders_2(sK2) & v2_lattice3(sK2) & v1_lattice3(sK2) & v5_orders_2(sK2) & v3_orders_2(sK2)),
% 19.60/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f31,f44,f43,f42])).
% 19.60/2.99  
% 19.60/2.99  fof(f74,plain,(
% 19.60/2.99    k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3),
% 19.60/2.99    inference(cnf_transformation,[],[f45])).
% 19.60/2.99  
% 19.60/2.99  fof(f67,plain,(
% 19.60/2.99    v3_orders_2(sK2)),
% 19.60/2.99    inference(cnf_transformation,[],[f45])).
% 19.60/2.99  
% 19.60/2.99  fof(f68,plain,(
% 19.60/2.99    v5_orders_2(sK2)),
% 19.60/2.99    inference(cnf_transformation,[],[f45])).
% 19.60/2.99  
% 19.60/2.99  fof(f69,plain,(
% 19.60/2.99    v1_lattice3(sK2)),
% 19.60/2.99    inference(cnf_transformation,[],[f45])).
% 19.60/2.99  
% 19.60/2.99  fof(f70,plain,(
% 19.60/2.99    v2_lattice3(sK2)),
% 19.60/2.99    inference(cnf_transformation,[],[f45])).
% 19.60/2.99  
% 19.60/2.99  fof(f71,plain,(
% 19.60/2.99    l1_orders_2(sK2)),
% 19.60/2.99    inference(cnf_transformation,[],[f45])).
% 19.60/2.99  
% 19.60/2.99  fof(f72,plain,(
% 19.60/2.99    m1_subset_1(sK3,u1_struct_0(sK2))),
% 19.60/2.99    inference(cnf_transformation,[],[f45])).
% 19.60/2.99  
% 19.60/2.99  fof(f73,plain,(
% 19.60/2.99    m1_subset_1(sK4,u1_struct_0(sK2))),
% 19.60/2.99    inference(cnf_transformation,[],[f45])).
% 19.60/2.99  
% 19.60/2.99  fof(f4,axiom,(
% 19.60/2.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 19.60/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.60/2.99  
% 19.60/2.99  fof(f18,plain,(
% 19.60/2.99    ! [X0,X1,X2] : (m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 19.60/2.99    inference(ennf_transformation,[],[f4])).
% 19.60/2.99  
% 19.60/2.99  fof(f19,plain,(
% 19.60/2.99    ! [X0,X1,X2] : (m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 19.60/2.99    inference(flattening,[],[f18])).
% 19.60/2.99  
% 19.60/2.99  fof(f49,plain,(
% 19.60/2.99    ( ! [X2,X0,X1] : (m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 19.60/2.99    inference(cnf_transformation,[],[f19])).
% 19.60/2.99  
% 19.60/2.99  fof(f8,axiom,(
% 19.60/2.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2))),
% 19.60/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.60/2.99  
% 19.60/2.99  fof(f26,plain,(
% 19.60/2.99    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 19.60/2.99    inference(ennf_transformation,[],[f8])).
% 19.60/2.99  
% 19.60/2.99  fof(f27,plain,(
% 19.60/2.99    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 19.60/2.99    inference(flattening,[],[f26])).
% 19.60/2.99  
% 19.60/2.99  fof(f65,plain,(
% 19.60/2.99    ( ! [X2,X0,X1] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 19.60/2.99    inference(cnf_transformation,[],[f27])).
% 19.60/2.99  
% 19.60/2.99  fof(f3,axiom,(
% 19.60/2.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 19.60/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.60/2.99  
% 19.60/2.99  fof(f16,plain,(
% 19.60/2.99    ! [X0,X1,X2] : (m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 19.60/2.99    inference(ennf_transformation,[],[f3])).
% 19.60/2.99  
% 19.60/2.99  fof(f17,plain,(
% 19.60/2.99    ! [X0,X1,X2] : (m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 19.60/2.99    inference(flattening,[],[f16])).
% 19.60/2.99  
% 19.60/2.99  fof(f48,plain,(
% 19.60/2.99    ( ! [X2,X0,X1] : (m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 19.60/2.99    inference(cnf_transformation,[],[f17])).
% 19.60/2.99  
% 19.60/2.99  fof(f9,axiom,(
% 19.60/2.99    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2)))),
% 19.60/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.60/2.99  
% 19.60/2.99  fof(f28,plain,(
% 19.60/2.99    ! [X0] : (! [X1] : (! [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)))),
% 19.60/2.99    inference(ennf_transformation,[],[f9])).
% 19.60/2.99  
% 19.60/2.99  fof(f29,plain,(
% 19.60/2.99    ! [X0] : (! [X1] : (! [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 19.60/2.99    inference(flattening,[],[f28])).
% 19.60/2.99  
% 19.60/2.99  fof(f66,plain,(
% 19.60/2.99    ( ! [X2,X0,X1] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)) )),
% 19.60/2.99    inference(cnf_transformation,[],[f29])).
% 19.60/2.99  
% 19.60/2.99  fof(f5,axiom,(
% 19.60/2.99    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 19.60/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.60/2.99  
% 19.60/2.99  fof(f20,plain,(
% 19.60/2.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 19.60/2.99    inference(ennf_transformation,[],[f5])).
% 19.60/2.99  
% 19.60/2.99  fof(f21,plain,(
% 19.60/2.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 19.60/2.99    inference(flattening,[],[f20])).
% 19.60/2.99  
% 19.60/2.99  fof(f32,plain,(
% 19.60/2.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3))) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 19.60/2.99    inference(nnf_transformation,[],[f21])).
% 19.60/2.99  
% 19.60/2.99  fof(f33,plain,(
% 19.60/2.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 19.60/2.99    inference(flattening,[],[f32])).
% 19.60/2.99  
% 19.60/2.99  fof(f34,plain,(
% 19.60/2.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 19.60/2.99    inference(rectify,[],[f33])).
% 19.60/2.99  
% 19.60/2.99  fof(f35,plain,(
% 19.60/2.99    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,X3,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))))),
% 19.60/2.99    introduced(choice_axiom,[])).
% 19.60/2.99  
% 19.60/2.99  fof(f36,plain,(
% 19.60/2.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,X3,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 19.60/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 19.60/2.99  
% 19.60/2.99  fof(f51,plain,(
% 19.60/2.99    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X2,X3) | k10_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 19.60/2.99    inference(cnf_transformation,[],[f36])).
% 19.60/2.99  
% 19.60/2.99  fof(f76,plain,(
% 19.60/2.99    ( ! [X2,X0,X1] : (r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 19.60/2.99    inference(equality_resolution,[],[f51])).
% 19.60/2.99  
% 19.60/2.99  fof(f1,axiom,(
% 19.60/2.99    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 19.60/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.60/2.99  
% 19.60/2.99  fof(f12,plain,(
% 19.60/2.99    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 19.60/2.99    inference(ennf_transformation,[],[f1])).
% 19.60/2.99  
% 19.60/2.99  fof(f13,plain,(
% 19.60/2.99    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 19.60/2.99    inference(flattening,[],[f12])).
% 19.60/2.99  
% 19.60/2.99  fof(f46,plain,(
% 19.60/2.99    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 19.60/2.99    inference(cnf_transformation,[],[f13])).
% 19.60/2.99  
% 19.60/2.99  fof(f50,plain,(
% 19.60/2.99    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X1,X3) | k10_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 19.60/2.99    inference(cnf_transformation,[],[f36])).
% 19.60/2.99  
% 19.60/2.99  fof(f77,plain,(
% 19.60/2.99    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 19.60/2.99    inference(equality_resolution,[],[f50])).
% 19.60/2.99  
% 19.60/2.99  cnf(c_11,plain,
% 19.60/2.99      ( ~ r1_orders_2(X0,X1,X2)
% 19.60/2.99      | ~ r1_orders_2(X0,X1,X3)
% 19.60/2.99      | ~ r1_orders_2(X0,sK1(X0,X3,X2,X1),X1)
% 19.60/2.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.60/2.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 19.60/2.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 19.60/2.99      | ~ v5_orders_2(X0)
% 19.60/2.99      | ~ v2_lattice3(X0)
% 19.60/2.99      | ~ l1_orders_2(X0)
% 19.60/2.99      | v2_struct_0(X0)
% 19.60/2.99      | k11_lattice3(X0,X3,X2) = X1 ),
% 19.60/2.99      inference(cnf_transformation,[],[f63]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_1,plain,
% 19.60/2.99      ( ~ v2_lattice3(X0) | ~ l1_orders_2(X0) | ~ v2_struct_0(X0) ),
% 19.60/2.99      inference(cnf_transformation,[],[f47]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_313,plain,
% 19.60/2.99      ( ~ l1_orders_2(X0)
% 19.60/2.99      | ~ v2_lattice3(X0)
% 19.60/2.99      | ~ v5_orders_2(X0)
% 19.60/2.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 19.60/2.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 19.60/2.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.60/2.99      | ~ r1_orders_2(X0,sK1(X0,X3,X2,X1),X1)
% 19.60/2.99      | ~ r1_orders_2(X0,X1,X3)
% 19.60/2.99      | ~ r1_orders_2(X0,X1,X2)
% 19.60/2.99      | k11_lattice3(X0,X3,X2) = X1 ),
% 19.60/2.99      inference(global_propositional_subsumption,
% 19.60/2.99                [status(thm)],
% 19.60/2.99                [c_11,c_1]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_314,plain,
% 19.60/2.99      ( ~ r1_orders_2(X0,X1,X2)
% 19.60/2.99      | ~ r1_orders_2(X0,X1,X3)
% 19.60/2.99      | ~ r1_orders_2(X0,sK1(X0,X2,X3,X1),X1)
% 19.60/2.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 19.60/2.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 19.60/2.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.60/2.99      | ~ v5_orders_2(X0)
% 19.60/2.99      | ~ v2_lattice3(X0)
% 19.60/2.99      | ~ l1_orders_2(X0)
% 19.60/2.99      | k11_lattice3(X0,X2,X3) = X1 ),
% 19.60/2.99      inference(renaming,[status(thm)],[c_313]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_451,plain,
% 19.60/2.99      ( ~ r1_orders_2(X0_46,X0_47,X1_47)
% 19.60/2.99      | ~ r1_orders_2(X0_46,X0_47,X2_47)
% 19.60/2.99      | ~ r1_orders_2(X0_46,sK1(X0_46,X1_47,X2_47,X0_47),X0_47)
% 19.60/2.99      | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ m1_subset_1(X2_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ v5_orders_2(X0_46)
% 19.60/2.99      | ~ v2_lattice3(X0_46)
% 19.60/2.99      | ~ l1_orders_2(X0_46)
% 19.60/2.99      | k11_lattice3(X0_46,X1_47,X2_47) = X0_47 ),
% 19.60/2.99      inference(subtyping,[status(esa)],[c_314]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_13,plain,
% 19.60/2.99      ( ~ r1_orders_2(X0,X1,X2)
% 19.60/2.99      | ~ r1_orders_2(X0,X1,X3)
% 19.60/2.99      | r1_orders_2(X0,sK1(X0,X3,X2,X1),X3)
% 19.60/2.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.60/2.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 19.60/2.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 19.60/2.99      | ~ v5_orders_2(X0)
% 19.60/2.99      | ~ v2_lattice3(X0)
% 19.60/2.99      | ~ l1_orders_2(X0)
% 19.60/2.99      | v2_struct_0(X0)
% 19.60/2.99      | k11_lattice3(X0,X3,X2) = X1 ),
% 19.60/2.99      inference(cnf_transformation,[],[f61]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_279,plain,
% 19.60/2.99      ( ~ l1_orders_2(X0)
% 19.60/2.99      | ~ v2_lattice3(X0)
% 19.60/2.99      | ~ v5_orders_2(X0)
% 19.60/2.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 19.60/2.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 19.60/2.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.60/2.99      | r1_orders_2(X0,sK1(X0,X3,X2,X1),X3)
% 19.60/2.99      | ~ r1_orders_2(X0,X1,X3)
% 19.60/2.99      | ~ r1_orders_2(X0,X1,X2)
% 19.60/2.99      | k11_lattice3(X0,X3,X2) = X1 ),
% 19.60/2.99      inference(global_propositional_subsumption,
% 19.60/2.99                [status(thm)],
% 19.60/2.99                [c_13,c_1]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_280,plain,
% 19.60/2.99      ( ~ r1_orders_2(X0,X1,X2)
% 19.60/2.99      | ~ r1_orders_2(X0,X1,X3)
% 19.60/2.99      | r1_orders_2(X0,sK1(X0,X2,X3,X1),X2)
% 19.60/2.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 19.60/2.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 19.60/2.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.60/2.99      | ~ v5_orders_2(X0)
% 19.60/2.99      | ~ v2_lattice3(X0)
% 19.60/2.99      | ~ l1_orders_2(X0)
% 19.60/2.99      | k11_lattice3(X0,X2,X3) = X1 ),
% 19.60/2.99      inference(renaming,[status(thm)],[c_279]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_455,plain,
% 19.60/2.99      ( ~ r1_orders_2(X0_46,X0_47,X1_47)
% 19.60/2.99      | ~ r1_orders_2(X0_46,X0_47,X2_47)
% 19.60/2.99      | r1_orders_2(X0_46,sK1(X0_46,X1_47,X2_47,X0_47),X1_47)
% 19.60/2.99      | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ m1_subset_1(X2_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ v5_orders_2(X0_46)
% 19.60/2.99      | ~ v2_lattice3(X0_46)
% 19.60/2.99      | ~ l1_orders_2(X0_46)
% 19.60/2.99      | k11_lattice3(X0_46,X1_47,X2_47) = X0_47 ),
% 19.60/2.99      inference(subtyping,[status(esa)],[c_280]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_39039,plain,
% 19.60/2.99      ( ~ r1_orders_2(X0_46,X0_47,X1_47)
% 19.60/2.99      | ~ r1_orders_2(X0_46,X0_47,X0_47)
% 19.60/2.99      | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ v5_orders_2(X0_46)
% 19.60/2.99      | ~ v2_lattice3(X0_46)
% 19.60/2.99      | ~ l1_orders_2(X0_46)
% 19.60/2.99      | k11_lattice3(X0_46,X0_47,X1_47) = X0_47 ),
% 19.60/2.99      inference(resolution,[status(thm)],[c_451,c_455]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_480,plain,
% 19.60/2.99      ( X0_47 != X1_47 | X2_47 != X1_47 | X2_47 = X0_47 ),
% 19.60/2.99      theory(equality) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_479,plain,( X0_47 = X0_47 ),theory(equality) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_1425,plain,
% 19.60/2.99      ( X0_47 != X1_47 | X1_47 = X0_47 ),
% 19.60/2.99      inference(resolution,[status(thm)],[c_480,c_479]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_43916,plain,
% 19.60/2.99      ( ~ r1_orders_2(X0_46,X0_47,X1_47)
% 19.60/2.99      | ~ r1_orders_2(X0_46,X0_47,X0_47)
% 19.60/2.99      | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ v5_orders_2(X0_46)
% 19.60/2.99      | ~ v2_lattice3(X0_46)
% 19.60/2.99      | ~ l1_orders_2(X0_46)
% 19.60/2.99      | X0_47 = k11_lattice3(X0_46,X0_47,X1_47) ),
% 19.60/2.99      inference(resolution,[status(thm)],[c_39039,c_1425]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_18,plain,
% 19.60/2.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 19.60/2.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 19.60/2.99      | ~ v5_orders_2(X1)
% 19.60/2.99      | ~ v2_lattice3(X1)
% 19.60/2.99      | ~ l1_orders_2(X1)
% 19.60/2.99      | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0) ),
% 19.60/2.99      inference(cnf_transformation,[],[f64]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_475,plain,
% 19.60/2.99      ( ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ v5_orders_2(X0_46)
% 19.60/2.99      | ~ v2_lattice3(X0_46)
% 19.60/2.99      | ~ l1_orders_2(X0_46)
% 19.60/2.99      | k11_lattice3(X0_46,X0_47,X1_47) = k12_lattice3(X0_46,X0_47,X1_47) ),
% 19.60/2.99      inference(subtyping,[status(esa)],[c_18]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_4030,plain,
% 19.60/2.99      ( ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ v5_orders_2(X0_46)
% 19.60/2.99      | ~ v2_lattice3(X0_46)
% 19.60/2.99      | ~ l1_orders_2(X0_46)
% 19.60/2.99      | k12_lattice3(X0_46,X1_47,X0_47) = k11_lattice3(X0_46,X1_47,X0_47) ),
% 19.60/2.99      inference(resolution,[status(thm)],[c_475,c_1425]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_4692,plain,
% 19.60/2.99      ( ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ v5_orders_2(X0_46)
% 19.60/2.99      | ~ v2_lattice3(X0_46)
% 19.60/2.99      | ~ l1_orders_2(X0_46)
% 19.60/2.99      | X2_47 != k11_lattice3(X0_46,X0_47,X1_47)
% 19.60/2.99      | k12_lattice3(X0_46,X0_47,X1_47) = X2_47 ),
% 19.60/2.99      inference(resolution,[status(thm)],[c_4030,c_480]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_45595,plain,
% 19.60/2.99      ( ~ r1_orders_2(X0_46,X0_47,X1_47)
% 19.60/2.99      | ~ r1_orders_2(X0_46,X0_47,X0_47)
% 19.60/2.99      | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ v5_orders_2(X0_46)
% 19.60/2.99      | ~ v2_lattice3(X0_46)
% 19.60/2.99      | ~ l1_orders_2(X0_46)
% 19.60/2.99      | k12_lattice3(X0_46,X0_47,X1_47) = X0_47 ),
% 19.60/2.99      inference(resolution,[status(thm)],[c_43916,c_4692]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_21,negated_conjecture,
% 19.60/2.99      ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
% 19.60/2.99      inference(cnf_transformation,[],[f74]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_472,negated_conjecture,
% 19.60/2.99      ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
% 19.60/2.99      inference(subtyping,[status(esa)],[c_21]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_46334,plain,
% 19.60/2.99      ( ~ r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4))
% 19.60/2.99      | ~ r1_orders_2(sK2,sK3,sK3)
% 19.60/2.99      | ~ m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 19.60/2.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 19.60/2.99      | ~ v5_orders_2(sK2)
% 19.60/2.99      | ~ v2_lattice3(sK2)
% 19.60/2.99      | ~ l1_orders_2(sK2) ),
% 19.60/2.99      inference(resolution,[status(thm)],[c_45595,c_472]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_28,negated_conjecture,
% 19.60/2.99      ( v3_orders_2(sK2) ),
% 19.60/2.99      inference(cnf_transformation,[],[f67]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_27,negated_conjecture,
% 19.60/2.99      ( v5_orders_2(sK2) ),
% 19.60/2.99      inference(cnf_transformation,[],[f68]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_26,negated_conjecture,
% 19.60/2.99      ( v1_lattice3(sK2) ),
% 19.60/2.99      inference(cnf_transformation,[],[f69]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_25,negated_conjecture,
% 19.60/2.99      ( v2_lattice3(sK2) ),
% 19.60/2.99      inference(cnf_transformation,[],[f70]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_24,negated_conjecture,
% 19.60/2.99      ( l1_orders_2(sK2) ),
% 19.60/2.99      inference(cnf_transformation,[],[f71]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_23,negated_conjecture,
% 19.60/2.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 19.60/2.99      inference(cnf_transformation,[],[f72]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_22,negated_conjecture,
% 19.60/2.99      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 19.60/2.99      inference(cnf_transformation,[],[f73]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_490,plain,
% 19.60/2.99      ( sK3 = sK3 ),
% 19.60/2.99      inference(instantiation,[status(thm)],[c_479]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_3,plain,
% 19.60/2.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 19.60/2.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 19.60/2.99      | m1_subset_1(k12_lattice3(X1,X2,X0),u1_struct_0(X1))
% 19.60/2.99      | ~ v5_orders_2(X1)
% 19.60/2.99      | ~ v2_lattice3(X1)
% 19.60/2.99      | ~ l1_orders_2(X1) ),
% 19.60/2.99      inference(cnf_transformation,[],[f49]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_476,plain,
% 19.60/2.99      ( ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
% 19.60/2.99      | m1_subset_1(k12_lattice3(X0_46,X0_47,X1_47),u1_struct_0(X0_46))
% 19.60/2.99      | ~ v5_orders_2(X0_46)
% 19.60/2.99      | ~ v2_lattice3(X0_46)
% 19.60/2.99      | ~ l1_orders_2(X0_46) ),
% 19.60/2.99      inference(subtyping,[status(esa)],[c_3]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_495,plain,
% 19.60/2.99      ( m1_subset_1(k12_lattice3(sK2,sK3,sK3),u1_struct_0(sK2))
% 19.60/2.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 19.60/2.99      | ~ v5_orders_2(sK2)
% 19.60/2.99      | ~ v2_lattice3(sK2)
% 19.60/2.99      | ~ l1_orders_2(sK2) ),
% 19.60/2.99      inference(instantiation,[status(thm)],[c_476]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_19,plain,
% 19.60/2.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 19.60/2.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 19.60/2.99      | ~ v5_orders_2(X1)
% 19.60/2.99      | ~ l1_orders_2(X1)
% 19.60/2.99      | ~ v1_lattice3(X1)
% 19.60/2.99      | k13_lattice3(X1,X2,X0) = k10_lattice3(X1,X2,X0) ),
% 19.60/2.99      inference(cnf_transformation,[],[f65]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_474,plain,
% 19.60/2.99      ( ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ v5_orders_2(X0_46)
% 19.60/2.99      | ~ l1_orders_2(X0_46)
% 19.60/2.99      | ~ v1_lattice3(X0_46)
% 19.60/2.99      | k13_lattice3(X0_46,X0_47,X1_47) = k10_lattice3(X0_46,X0_47,X1_47) ),
% 19.60/2.99      inference(subtyping,[status(esa)],[c_19]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_1542,plain,
% 19.60/2.99      ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 19.60/2.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 19.60/2.99      | ~ v5_orders_2(sK2)
% 19.60/2.99      | ~ l1_orders_2(sK2)
% 19.60/2.99      | ~ v1_lattice3(sK2)
% 19.60/2.99      | k13_lattice3(sK2,sK3,sK4) = k10_lattice3(sK2,sK3,sK4) ),
% 19.60/2.99      inference(instantiation,[status(thm)],[c_474]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_2,plain,
% 19.60/2.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 19.60/2.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 19.60/2.99      | m1_subset_1(k10_lattice3(X1,X2,X0),u1_struct_0(X1))
% 19.60/2.99      | ~ l1_orders_2(X1) ),
% 19.60/2.99      inference(cnf_transformation,[],[f48]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_477,plain,
% 19.60/2.99      ( ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
% 19.60/2.99      | m1_subset_1(k10_lattice3(X0_46,X0_47,X1_47),u1_struct_0(X0_46))
% 19.60/2.99      | ~ l1_orders_2(X0_46) ),
% 19.60/2.99      inference(subtyping,[status(esa)],[c_2]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_7503,plain,
% 19.60/2.99      ( m1_subset_1(k10_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 19.60/2.99      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 19.60/2.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 19.60/2.99      | ~ l1_orders_2(sK2) ),
% 19.60/2.99      inference(instantiation,[status(thm)],[c_477]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_20,plain,
% 19.60/2.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 19.60/2.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 19.60/2.99      | ~ v3_orders_2(X1)
% 19.60/2.99      | ~ v5_orders_2(X1)
% 19.60/2.99      | ~ v2_lattice3(X1)
% 19.60/2.99      | ~ l1_orders_2(X1)
% 19.60/2.99      | ~ v1_lattice3(X1)
% 19.60/2.99      | k13_lattice3(X1,k12_lattice3(X1,X2,X0),X0) = X0 ),
% 19.60/2.99      inference(cnf_transformation,[],[f66]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_473,plain,
% 19.60/2.99      ( ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ v3_orders_2(X0_46)
% 19.60/2.99      | ~ v5_orders_2(X0_46)
% 19.60/2.99      | ~ v2_lattice3(X0_46)
% 19.60/2.99      | ~ l1_orders_2(X0_46)
% 19.60/2.99      | ~ v1_lattice3(X0_46)
% 19.60/2.99      | k13_lattice3(X0_46,k12_lattice3(X0_46,X0_47,X1_47),X1_47) = X1_47 ),
% 19.60/2.99      inference(subtyping,[status(esa)],[c_20]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_4291,plain,
% 19.60/2.99      ( ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ v3_orders_2(X0_46)
% 19.60/2.99      | ~ v5_orders_2(X0_46)
% 19.60/2.99      | ~ v2_lattice3(X0_46)
% 19.60/2.99      | ~ l1_orders_2(X0_46)
% 19.60/2.99      | ~ v1_lattice3(X0_46)
% 19.60/2.99      | X0_47 = k13_lattice3(X0_46,k12_lattice3(X0_46,X1_47,X0_47),X0_47) ),
% 19.60/2.99      inference(resolution,[status(thm)],[c_473,c_1425]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_483,plain,
% 19.60/2.99      ( ~ r1_orders_2(X0_46,X0_47,X1_47)
% 19.60/2.99      | r1_orders_2(X0_46,X2_47,X3_47)
% 19.60/2.99      | X2_47 != X0_47
% 19.60/2.99      | X3_47 != X1_47 ),
% 19.60/2.99      theory(equality) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_8010,plain,
% 19.60/2.99      ( r1_orders_2(X0_46,X0_47,X1_47)
% 19.60/2.99      | ~ r1_orders_2(X0_46,X2_47,k13_lattice3(X1_46,k12_lattice3(X1_46,X3_47,X1_47),X1_47))
% 19.60/2.99      | ~ m1_subset_1(X1_47,u1_struct_0(X1_46))
% 19.60/2.99      | ~ m1_subset_1(X3_47,u1_struct_0(X1_46))
% 19.60/2.99      | ~ v3_orders_2(X1_46)
% 19.60/2.99      | ~ v5_orders_2(X1_46)
% 19.60/2.99      | ~ v2_lattice3(X1_46)
% 19.60/2.99      | ~ l1_orders_2(X1_46)
% 19.60/2.99      | ~ v1_lattice3(X1_46)
% 19.60/2.99      | X0_47 != X2_47 ),
% 19.60/2.99      inference(resolution,[status(thm)],[c_4291,c_483]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_3603,plain,
% 19.60/2.99      ( r1_orders_2(X0_46,X0_47,k13_lattice3(X1_46,X1_47,X2_47))
% 19.60/2.99      | ~ r1_orders_2(X0_46,X3_47,k10_lattice3(X1_46,X1_47,X2_47))
% 19.60/2.99      | ~ m1_subset_1(X2_47,u1_struct_0(X1_46))
% 19.60/2.99      | ~ m1_subset_1(X1_47,u1_struct_0(X1_46))
% 19.60/2.99      | ~ v5_orders_2(X1_46)
% 19.60/2.99      | ~ l1_orders_2(X1_46)
% 19.60/2.99      | ~ v1_lattice3(X1_46)
% 19.60/2.99      | X0_47 != X3_47 ),
% 19.60/2.99      inference(resolution,[status(thm)],[c_474,c_483]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_9,plain,
% 19.60/2.99      ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
% 19.60/2.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 19.60/2.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.60/2.99      | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
% 19.60/2.99      | ~ v5_orders_2(X0)
% 19.60/2.99      | ~ l1_orders_2(X0)
% 19.60/2.99      | ~ v1_lattice3(X0)
% 19.60/2.99      | v2_struct_0(X0) ),
% 19.60/2.99      inference(cnf_transformation,[],[f76]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_0,plain,
% 19.60/2.99      ( ~ l1_orders_2(X0) | ~ v1_lattice3(X0) | ~ v2_struct_0(X0) ),
% 19.60/2.99      inference(cnf_transformation,[],[f46]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_204,plain,
% 19.60/2.99      ( ~ v1_lattice3(X0)
% 19.60/2.99      | ~ l1_orders_2(X0)
% 19.60/2.99      | ~ v5_orders_2(X0)
% 19.60/2.99      | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
% 19.60/2.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.60/2.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 19.60/2.99      | r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1)) ),
% 19.60/2.99      inference(global_propositional_subsumption,[status(thm)],[c_9,c_0]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_205,plain,
% 19.60/2.99      ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
% 19.60/2.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.60/2.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 19.60/2.99      | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
% 19.60/2.99      | ~ v5_orders_2(X0)
% 19.60/2.99      | ~ l1_orders_2(X0)
% 19.60/2.99      | ~ v1_lattice3(X0) ),
% 19.60/2.99      inference(renaming,[status(thm)],[c_204]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_464,plain,
% 19.60/2.99      ( r1_orders_2(X0_46,X0_47,k10_lattice3(X0_46,X1_47,X0_47))
% 19.60/2.99      | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ m1_subset_1(k10_lattice3(X0_46,X1_47,X0_47),u1_struct_0(X0_46))
% 19.60/2.99      | ~ v5_orders_2(X0_46)
% 19.60/2.99      | ~ l1_orders_2(X0_46)
% 19.60/2.99      | ~ v1_lattice3(X0_46) ),
% 19.60/2.99      inference(subtyping,[status(esa)],[c_205]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_1526,plain,
% 19.60/2.99      ( r1_orders_2(X0_46,X0_47,k10_lattice3(X0_46,X1_47,X0_47))
% 19.60/2.99      | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ v5_orders_2(X0_46)
% 19.60/2.99      | ~ l1_orders_2(X0_46)
% 19.60/2.99      | ~ v1_lattice3(X0_46) ),
% 19.60/2.99      inference(backward_subsumption_resolution,
% 19.60/2.99                [status(thm)],
% 19.60/2.99                [c_477,c_464]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_9481,plain,
% 19.60/2.99      ( r1_orders_2(X0_46,X0_47,k13_lattice3(X0_46,X1_47,X2_47))
% 19.60/2.99      | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ m1_subset_1(X2_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ v5_orders_2(X0_46)
% 19.60/2.99      | ~ l1_orders_2(X0_46)
% 19.60/2.99      | ~ v1_lattice3(X0_46)
% 19.60/2.99      | X0_47 != X2_47 ),
% 19.60/2.99      inference(resolution,[status(thm)],[c_3603,c_1526]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_28666,plain,
% 19.60/2.99      ( r1_orders_2(X0_46,X0_47,X1_47)
% 19.60/2.99      | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ m1_subset_1(X2_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ m1_subset_1(k12_lattice3(X0_46,X2_47,X1_47),u1_struct_0(X0_46))
% 19.60/2.99      | ~ v3_orders_2(X0_46)
% 19.60/2.99      | ~ v5_orders_2(X0_46)
% 19.60/2.99      | ~ v2_lattice3(X0_46)
% 19.60/2.99      | ~ l1_orders_2(X0_46)
% 19.60/2.99      | ~ v1_lattice3(X0_46)
% 19.60/2.99      | X3_47 != X1_47
% 19.60/2.99      | X0_47 != X3_47 ),
% 19.60/2.99      inference(resolution,[status(thm)],[c_8010,c_9481]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_28668,plain,
% 19.60/2.99      ( r1_orders_2(sK2,sK3,sK3)
% 19.60/2.99      | ~ m1_subset_1(k12_lattice3(sK2,sK3,sK3),u1_struct_0(sK2))
% 19.60/2.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 19.60/2.99      | ~ v3_orders_2(sK2)
% 19.60/2.99      | ~ v5_orders_2(sK2)
% 19.60/2.99      | ~ v2_lattice3(sK2)
% 19.60/2.99      | ~ l1_orders_2(sK2)
% 19.60/2.99      | ~ v1_lattice3(sK2)
% 19.60/2.99      | sK3 != sK3 ),
% 19.60/2.99      inference(instantiation,[status(thm)],[c_28666]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_481,plain,
% 19.60/2.99      ( ~ m1_subset_1(X0_47,X0_48)
% 19.60/2.99      | m1_subset_1(X1_47,X0_48)
% 19.60/2.99      | X1_47 != X0_47 ),
% 19.60/2.99      theory(equality) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_1338,plain,
% 19.60/2.99      ( m1_subset_1(X0_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ m1_subset_1(k10_lattice3(X0_46,X1_47,X2_47),u1_struct_0(X0_46))
% 19.60/2.99      | X0_47 != k10_lattice3(X0_46,X1_47,X2_47) ),
% 19.60/2.99      inference(instantiation,[status(thm)],[c_481]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_3634,plain,
% 19.60/2.99      ( m1_subset_1(k13_lattice3(sK2,X0_47,X1_47),u1_struct_0(sK2))
% 19.60/2.99      | ~ m1_subset_1(k10_lattice3(sK2,X2_47,X3_47),u1_struct_0(sK2))
% 19.60/2.99      | k13_lattice3(sK2,X0_47,X1_47) != k10_lattice3(sK2,X2_47,X3_47) ),
% 19.60/2.99      inference(instantiation,[status(thm)],[c_1338]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_8109,plain,
% 19.60/2.99      ( m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 19.60/2.99      | ~ m1_subset_1(k10_lattice3(sK2,X0_47,X1_47),u1_struct_0(sK2))
% 19.60/2.99      | k13_lattice3(sK2,sK3,sK4) != k10_lattice3(sK2,X0_47,X1_47) ),
% 19.60/2.99      inference(instantiation,[status(thm)],[c_3634]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_32071,plain,
% 19.60/2.99      ( m1_subset_1(k13_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 19.60/2.99      | ~ m1_subset_1(k10_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 19.60/2.99      | k13_lattice3(sK2,sK3,sK4) != k10_lattice3(sK2,sK3,sK4) ),
% 19.60/2.99      inference(instantiation,[status(thm)],[c_8109]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_46989,plain,
% 19.60/2.99      ( ~ r1_orders_2(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) ),
% 19.60/2.99      inference(global_propositional_subsumption,
% 19.60/2.99                [status(thm)],
% 19.60/2.99                [c_46334,c_28,c_27,c_26,c_25,c_24,c_23,c_22,c_490,c_495,
% 19.60/2.99                 c_1542,c_7503,c_28668,c_32071]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_10,plain,
% 19.60/2.99      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 19.60/2.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.60/2.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 19.60/2.99      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 19.60/2.99      | ~ v5_orders_2(X0)
% 19.60/2.99      | ~ l1_orders_2(X0)
% 19.60/2.99      | ~ v1_lattice3(X0)
% 19.60/2.99      | v2_struct_0(X0) ),
% 19.60/2.99      inference(cnf_transformation,[],[f77]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_213,plain,
% 19.60/2.99      ( ~ v1_lattice3(X0)
% 19.60/2.99      | ~ l1_orders_2(X0)
% 19.60/2.99      | ~ v5_orders_2(X0)
% 19.60/2.99      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 19.60/2.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 19.60/2.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.60/2.99      | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) ),
% 19.60/2.99      inference(global_propositional_subsumption,
% 19.60/2.99                [status(thm)],
% 19.60/2.99                [c_10,c_0]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_214,plain,
% 19.60/2.99      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 19.60/2.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.60/2.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 19.60/2.99      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 19.60/2.99      | ~ v5_orders_2(X0)
% 19.60/2.99      | ~ l1_orders_2(X0)
% 19.60/2.99      | ~ v1_lattice3(X0) ),
% 19.60/2.99      inference(renaming,[status(thm)],[c_213]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_463,plain,
% 19.60/2.99      ( r1_orders_2(X0_46,X0_47,k10_lattice3(X0_46,X0_47,X1_47))
% 19.60/2.99      | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ m1_subset_1(k10_lattice3(X0_46,X0_47,X1_47),u1_struct_0(X0_46))
% 19.60/2.99      | ~ v5_orders_2(X0_46)
% 19.60/2.99      | ~ l1_orders_2(X0_46)
% 19.60/2.99      | ~ v1_lattice3(X0_46) ),
% 19.60/2.99      inference(subtyping,[status(esa)],[c_214]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_634,plain,
% 19.60/2.99      ( ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
% 19.60/2.99      | r1_orders_2(X0_46,X0_47,k10_lattice3(X0_46,X0_47,X1_47))
% 19.60/2.99      | ~ v5_orders_2(X0_46)
% 19.60/2.99      | ~ l1_orders_2(X0_46)
% 19.60/2.99      | ~ v1_lattice3(X0_46) ),
% 19.60/2.99      inference(global_propositional_subsumption,
% 19.60/2.99                [status(thm)],
% 19.60/2.99                [c_463,c_477]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_635,plain,
% 19.60/2.99      ( r1_orders_2(X0_46,X0_47,k10_lattice3(X0_46,X0_47,X1_47))
% 19.60/2.99      | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ m1_subset_1(X0_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ v5_orders_2(X0_46)
% 19.60/2.99      | ~ l1_orders_2(X0_46)
% 19.60/2.99      | ~ v1_lattice3(X0_46) ),
% 19.60/2.99      inference(renaming,[status(thm)],[c_634]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_9477,plain,
% 19.60/2.99      ( r1_orders_2(X0_46,X0_47,k13_lattice3(X0_46,X1_47,X2_47))
% 19.60/2.99      | ~ m1_subset_1(X1_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ m1_subset_1(X2_47,u1_struct_0(X0_46))
% 19.60/2.99      | ~ v5_orders_2(X0_46)
% 19.60/2.99      | ~ l1_orders_2(X0_46)
% 19.60/2.99      | ~ v1_lattice3(X0_46)
% 19.60/2.99      | X0_47 != X1_47 ),
% 19.60/2.99      inference(resolution,[status(thm)],[c_3603,c_635]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_47001,plain,
% 19.60/2.99      ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 19.60/2.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 19.60/2.99      | ~ v5_orders_2(sK2)
% 19.60/2.99      | ~ l1_orders_2(sK2)
% 19.60/2.99      | ~ v1_lattice3(sK2)
% 19.60/2.99      | sK3 != sK3 ),
% 19.60/2.99      inference(resolution,[status(thm)],[c_46989,c_9477]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(c_47004,plain,
% 19.60/2.99      ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 19.60/2.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 19.60/2.99      | ~ v5_orders_2(sK2)
% 19.60/2.99      | ~ l1_orders_2(sK2)
% 19.60/2.99      | ~ v1_lattice3(sK2) ),
% 19.60/2.99      inference(equality_resolution_simp,[status(thm)],[c_47001]) ).
% 19.60/2.99  
% 19.60/2.99  cnf(contradiction,plain,
% 19.60/2.99      ( $false ),
% 19.60/2.99      inference(minisat,[status(thm)],[c_47004,c_22,c_23,c_24,c_26,c_27]) ).
% 19.60/2.99  
% 19.60/2.99  
% 19.60/2.99  % SZS output end CNFRefutation for theBenchmark.p
% 19.60/2.99  
% 19.60/2.99  ------                               Statistics
% 19.60/2.99  
% 19.60/2.99  ------ Selected
% 19.60/2.99  
% 19.60/2.99  total_time:                             2.059
% 19.60/2.99  
%------------------------------------------------------------------------------
