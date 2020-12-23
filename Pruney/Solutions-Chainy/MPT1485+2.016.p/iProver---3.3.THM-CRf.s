%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:06 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 415 expanded)
%              Number of clauses        :   85 ( 113 expanded)
%              Number of leaves         :   16 ( 125 expanded)
%              Depth                    :   18
%              Number of atoms          :  849 (2765 expanded)
%              Number of equality atoms :  134 ( 427 expanded)
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

fof(f34,plain,(
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
    inference(flattening,[],[f34])).

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
    inference(rectify,[],[f35])).

fof(f37,plain,(
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

fof(f38,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f37])).

fof(f60,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

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

fof(f41,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,sK4)) != X1
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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

fof(f39,plain,
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

fof(f42,plain,
    ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_orders_2(sK2)
    & v2_lattice3(sK2)
    & v1_lattice3(sK2)
    & v5_orders_2(sK2)
    & v3_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f28,f41,f40,f39])).

fof(f66,plain,(
    v2_lattice3(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f64,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f67,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f58,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

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

fof(f29,plain,(
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
    inference(flattening,[],[f29])).

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
    inference(rectify,[],[f30])).

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f47,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f65,plain,(
    v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f63,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
    inference(cnf_transformation,[],[f42])).

fof(f69,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f42])).

fof(f68,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1138,plain,
    ( X0_47 != X1_47
    | X2_47 != X1_47
    | X2_47 = X0_47 ),
    theory(equality)).

cnf(c_4743,plain,
    ( X0_47 != X1_47
    | X0_47 = k11_lattice3(sK2,X2_47,k10_lattice3(sK2,sK3,sK4))
    | k11_lattice3(sK2,X2_47,k10_lattice3(sK2,sK3,sK4)) != X1_47 ),
    inference(instantiation,[status(thm)],[c_1138])).

cnf(c_4744,plain,
    ( k11_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,sK4)) != sK3
    | sK3 = k11_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,sK4))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_4743])).

cnf(c_11,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK1(X0,X3,X2,X1),X1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1,plain,
    ( ~ v2_lattice3(X0)
    | ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_189,plain,
    ( ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r1_orders_2(X0,sK1(X0,X3,X2,X1),X1)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_1])).

cnf(c_190,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK1(X0,X2,X3,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X2,X3) = X1 ),
    inference(renaming,[status(thm)],[c_189])).

cnf(c_24,negated_conjecture,
    ( v2_lattice3(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_348,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK1(X0,X3,X2,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_190,c_24])).

cnf(c_349,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | ~ r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k11_lattice3(sK2,X1,X2) = X0 ),
    inference(unflattening,[status(thm)],[c_348])).

cnf(c_26,negated_conjecture,
    ( v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_23,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_353,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | ~ r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k11_lattice3(sK2,X1,X2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_349,c_26,c_23])).

cnf(c_354,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | ~ r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | k11_lattice3(sK2,X1,X2) = X0 ),
    inference(renaming,[status(thm)],[c_353])).

cnf(c_1131,plain,
    ( ~ r1_orders_2(sK2,X0_47,X1_47)
    | ~ r1_orders_2(sK2,X0_47,X2_47)
    | ~ r1_orders_2(sK2,sK1(sK2,X1_47,X2_47,X0_47),X0_47)
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X2_47,u1_struct_0(sK2))
    | k11_lattice3(sK2,X1_47,X2_47) = X0_47 ),
    inference(subtyping,[status(esa)],[c_354])).

cnf(c_4513,plain,
    ( ~ r1_orders_2(sK2,sK1(sK2,X0_47,k10_lattice3(sK2,sK3,sK4),sK3),sK3)
    | ~ r1_orders_2(sK2,sK3,X0_47)
    | ~ r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK4))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k11_lattice3(sK2,X0_47,k10_lattice3(sK2,sK3,sK4)) = sK3 ),
    inference(instantiation,[status(thm)],[c_1131])).

cnf(c_4530,plain,
    ( ~ r1_orders_2(sK2,sK1(sK2,sK3,k10_lattice3(sK2,sK3,sK4),sK3),sK3)
    | ~ r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK4))
    | ~ r1_orders_2(sK2,sK3,sK3)
    | ~ m1_subset_1(k10_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k11_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,sK4)) = sK3 ),
    inference(instantiation,[status(thm)],[c_4513])).

cnf(c_13,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK1(X0,X3,X2,X1),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_177,plain,
    ( ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | r1_orders_2(X0,sK1(X0,X3,X2,X1),X3)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_1])).

cnf(c_178,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK1(X0,X2,X3,X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X2,X3) = X1 ),
    inference(renaming,[status(thm)],[c_177])).

cnf(c_414,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK1(X0,X3,X2,X1),X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k11_lattice3(X0,X3,X2) = X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_178,c_24])).

cnf(c_415,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k11_lattice3(sK2,X1,X2) = X0 ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_417,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k11_lattice3(sK2,X1,X2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_415,c_26,c_23])).

cnf(c_418,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | k11_lattice3(sK2,X1,X2) = X0 ),
    inference(renaming,[status(thm)],[c_417])).

cnf(c_1129,plain,
    ( ~ r1_orders_2(sK2,X0_47,X1_47)
    | ~ r1_orders_2(sK2,X0_47,X2_47)
    | r1_orders_2(sK2,sK1(sK2,X1_47,X2_47,X0_47),X1_47)
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X2_47,u1_struct_0(sK2))
    | k11_lattice3(sK2,X1_47,X2_47) = X0_47 ),
    inference(subtyping,[status(esa)],[c_418])).

cnf(c_4515,plain,
    ( r1_orders_2(sK2,sK1(sK2,X0_47,k10_lattice3(sK2,sK3,sK4),sK3),X0_47)
    | ~ r1_orders_2(sK2,sK3,X0_47)
    | ~ r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK4))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k11_lattice3(sK2,X0_47,k10_lattice3(sK2,sK3,sK4)) = sK3 ),
    inference(instantiation,[status(thm)],[c_1129])).

cnf(c_4522,plain,
    ( r1_orders_2(sK2,sK1(sK2,sK3,k10_lattice3(sK2,sK3,sK4),sK3),sK3)
    | ~ r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK4))
    | ~ r1_orders_2(sK2,sK3,sK3)
    | ~ m1_subset_1(k10_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k11_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,sK4)) = sK3 ),
    inference(instantiation,[status(thm)],[c_4515])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k10_lattice3(X1,X0,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_946,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k10_lattice3(X1,X0,X2),u1_struct_0(X1))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_23])).

cnf(c_947,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_946])).

cnf(c_10,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | ~ v5_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_553,plain,
    ( ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_24])).

cnf(c_554,plain,
    ( ~ v2_struct_0(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_553])).

cnf(c_82,plain,
    ( ~ v2_lattice3(sK2)
    | ~ v2_struct_0(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_556,plain,
    ( ~ v2_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_554,c_24,c_23,c_82])).

cnf(c_666,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_556])).

cnf(c_667,plain,
    ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2))
    | ~ v1_lattice3(sK2)
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_666])).

cnf(c_25,negated_conjecture,
    ( v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_671,plain,
    ( ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_667,c_26,c_25,c_23])).

cnf(c_672,plain,
    ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_671])).

cnf(c_965,plain,
    ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_947,c_672])).

cnf(c_1115,plain,
    ( r1_orders_2(sK2,X0_47,k10_lattice3(sK2,X0_47,X1_47))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_965])).

cnf(c_2645,plain,
    ( r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK4))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1115])).

cnf(c_1934,plain,
    ( X0_47 != X1_47
    | k12_lattice3(sK2,X2_47,X3_47) != X1_47
    | k12_lattice3(sK2,X2_47,X3_47) = X0_47 ),
    inference(instantiation,[status(thm)],[c_1138])).

cnf(c_2521,plain,
    ( X0_47 != k11_lattice3(sK2,X1_47,k10_lattice3(sK2,sK3,sK4))
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_47
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k11_lattice3(sK2,X1_47,k10_lattice3(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1934])).

cnf(c_2522,plain,
    ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k11_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,sK4))
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
    | sK3 != k11_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2521])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,X0,X2) = k12_lattice3(X1,X0,X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_564,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,X0,X2) = k12_lattice3(X1,X0,X2)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_24])).

cnf(c_565,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | k11_lattice3(sK2,X0,X1) = k12_lattice3(sK2,X0,X1) ),
    inference(unflattening,[status(thm)],[c_564])).

cnf(c_569,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k11_lattice3(sK2,X0,X1) = k12_lattice3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_565,c_26,c_23])).

cnf(c_570,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k11_lattice3(sK2,X1,X0) = k12_lattice3(sK2,X1,X0) ),
    inference(renaming,[status(thm)],[c_569])).

cnf(c_1124,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | k11_lattice3(sK2,X1_47,X0_47) = k12_lattice3(sK2,X1_47,X0_47) ),
    inference(subtyping,[status(esa)],[c_570])).

cnf(c_2160,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(k10_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | k11_lattice3(sK2,X0_47,k10_lattice3(sK2,sK3,sK4)) = k12_lattice3(sK2,X0_47,k10_lattice3(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1124])).

cnf(c_2163,plain,
    ( ~ m1_subset_1(k10_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k11_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,sK4)) = k12_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2160])).

cnf(c_1798,plain,
    ( X0_47 != X1_47
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != X1_47
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_47 ),
    inference(instantiation,[status(thm)],[c_1138])).

cnf(c_1908,plain,
    ( X0_47 != k12_lattice3(sK2,X1_47,k10_lattice3(sK2,sK3,sK4))
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_47
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k12_lattice3(sK2,X1_47,k10_lattice3(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1798])).

cnf(c_2159,plain,
    ( k11_lattice3(sK2,X0_47,k10_lattice3(sK2,sK3,sK4)) != k12_lattice3(sK2,X0_47,k10_lattice3(sK2,sK3,sK4))
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = k11_lattice3(sK2,X0_47,k10_lattice3(sK2,sK3,sK4))
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k12_lattice3(sK2,X0_47,k10_lattice3(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1908])).

cnf(c_2161,plain,
    ( k11_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,sK4)) != k12_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,sK4))
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = k11_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,sK4))
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k12_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2159])).

cnf(c_1117,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | m1_subset_1(k10_lattice3(sK2,X0_47,X1_47),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_947])).

cnf(c_2083,plain,
    ( m1_subset_1(k10_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1117])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k13_lattice3(X1,X0,X2) = k10_lattice3(X1,X0,X2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_921,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k13_lattice3(X1,X0,X2) = k10_lattice3(X1,X0,X2)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_26])).

cnf(c_922,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v1_lattice3(sK2)
    | ~ l1_orders_2(sK2)
    | k13_lattice3(sK2,X0,X1) = k10_lattice3(sK2,X0,X1) ),
    inference(unflattening,[status(thm)],[c_921])).

cnf(c_926,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k13_lattice3(sK2,X0,X1) = k10_lattice3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_922,c_25,c_23])).

cnf(c_927,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k13_lattice3(sK2,X1,X0) = k10_lattice3(sK2,X1,X0) ),
    inference(renaming,[status(thm)],[c_926])).

cnf(c_1118,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | k13_lattice3(sK2,X1_47,X0_47) = k10_lattice3(sK2,X1_47,X0_47) ),
    inference(subtyping,[status(esa)],[c_927])).

cnf(c_1883,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | k13_lattice3(sK2,sK3,sK4) = k10_lattice3(sK2,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1118])).

cnf(c_1141,plain,
    ( X0_47 != X1_47
    | X2_47 != X3_47
    | k12_lattice3(X0_46,X0_47,X2_47) = k12_lattice3(X0_46,X1_47,X3_47) ),
    theory(equality)).

cnf(c_1800,plain,
    ( k13_lattice3(sK2,sK3,sK4) != X0_47
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = k12_lattice3(sK2,X1_47,X0_47)
    | sK3 != X1_47 ),
    inference(instantiation,[status(thm)],[c_1141])).

cnf(c_1882,plain,
    ( k13_lattice3(sK2,sK3,sK4) != k10_lattice3(sK2,sK3,sK4)
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = k12_lattice3(sK2,X0_47,k10_lattice3(sK2,sK3,sK4))
    | sK3 != X0_47 ),
    inference(instantiation,[status(thm)],[c_1800])).

cnf(c_1884,plain,
    ( k13_lattice3(sK2,sK3,sK4) != k10_lattice3(sK2,sK3,sK4)
    | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = k12_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,sK4))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1882])).

cnf(c_0,plain,
    ( r1_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_27,negated_conjecture,
    ( v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_327,plain,
    ( r1_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_27])).

cnf(c_328,plain,
    ( r1_orders_2(sK2,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_332,plain,
    ( r1_orders_2(sK2,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_328,c_24,c_23,c_82])).

cnf(c_1132,plain,
    ( r1_orders_2(sK2,X0_47,X0_47)
    | ~ m1_subset_1(X0_47,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_332])).

cnf(c_1152,plain,
    ( r1_orders_2(sK2,sK3,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1132])).

cnf(c_20,negated_conjecture,
    ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1135,negated_conjecture,
    ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1137,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_1148,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1137])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f68])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4744,c_4530,c_4522,c_2645,c_2522,c_2163,c_2161,c_2083,c_1883,c_1884,c_1152,c_1135,c_1148,c_21,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:04:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.78/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.03  
% 2.78/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.78/1.03  
% 2.78/1.03  ------  iProver source info
% 2.78/1.03  
% 2.78/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.78/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.78/1.03  git: non_committed_changes: false
% 2.78/1.03  git: last_make_outside_of_git: false
% 2.78/1.03  
% 2.78/1.03  ------ 
% 2.78/1.03  
% 2.78/1.03  ------ Input Options
% 2.78/1.03  
% 2.78/1.03  --out_options                           all
% 2.78/1.03  --tptp_safe_out                         true
% 2.78/1.03  --problem_path                          ""
% 2.78/1.03  --include_path                          ""
% 2.78/1.03  --clausifier                            res/vclausify_rel
% 2.78/1.03  --clausifier_options                    --mode clausify
% 2.78/1.03  --stdin                                 false
% 2.78/1.03  --stats_out                             all
% 2.78/1.03  
% 2.78/1.03  ------ General Options
% 2.78/1.03  
% 2.78/1.03  --fof                                   false
% 2.78/1.03  --time_out_real                         305.
% 2.78/1.03  --time_out_virtual                      -1.
% 2.78/1.03  --symbol_type_check                     false
% 2.78/1.03  --clausify_out                          false
% 2.78/1.03  --sig_cnt_out                           false
% 2.78/1.03  --trig_cnt_out                          false
% 2.78/1.03  --trig_cnt_out_tolerance                1.
% 2.78/1.03  --trig_cnt_out_sk_spl                   false
% 2.78/1.03  --abstr_cl_out                          false
% 2.78/1.03  
% 2.78/1.03  ------ Global Options
% 2.78/1.03  
% 2.78/1.03  --schedule                              default
% 2.78/1.03  --add_important_lit                     false
% 2.78/1.03  --prop_solver_per_cl                    1000
% 2.78/1.03  --min_unsat_core                        false
% 2.78/1.03  --soft_assumptions                      false
% 2.78/1.03  --soft_lemma_size                       3
% 2.78/1.03  --prop_impl_unit_size                   0
% 2.78/1.03  --prop_impl_unit                        []
% 2.78/1.03  --share_sel_clauses                     true
% 2.78/1.03  --reset_solvers                         false
% 2.78/1.03  --bc_imp_inh                            [conj_cone]
% 2.78/1.03  --conj_cone_tolerance                   3.
% 2.78/1.03  --extra_neg_conj                        none
% 2.78/1.03  --large_theory_mode                     true
% 2.78/1.03  --prolific_symb_bound                   200
% 2.78/1.03  --lt_threshold                          2000
% 2.78/1.03  --clause_weak_htbl                      true
% 2.78/1.03  --gc_record_bc_elim                     false
% 2.78/1.03  
% 2.78/1.03  ------ Preprocessing Options
% 2.78/1.03  
% 2.78/1.03  --preprocessing_flag                    true
% 2.78/1.03  --time_out_prep_mult                    0.1
% 2.78/1.03  --splitting_mode                        input
% 2.78/1.03  --splitting_grd                         true
% 2.78/1.03  --splitting_cvd                         false
% 2.78/1.03  --splitting_cvd_svl                     false
% 2.78/1.03  --splitting_nvd                         32
% 2.78/1.03  --sub_typing                            true
% 2.78/1.03  --prep_gs_sim                           true
% 2.78/1.03  --prep_unflatten                        true
% 2.78/1.03  --prep_res_sim                          true
% 2.78/1.03  --prep_upred                            true
% 2.78/1.03  --prep_sem_filter                       exhaustive
% 2.78/1.03  --prep_sem_filter_out                   false
% 2.78/1.03  --pred_elim                             true
% 2.78/1.03  --res_sim_input                         true
% 2.78/1.03  --eq_ax_congr_red                       true
% 2.78/1.03  --pure_diseq_elim                       true
% 2.78/1.03  --brand_transform                       false
% 2.78/1.03  --non_eq_to_eq                          false
% 2.78/1.03  --prep_def_merge                        true
% 2.78/1.03  --prep_def_merge_prop_impl              false
% 2.78/1.03  --prep_def_merge_mbd                    true
% 2.78/1.03  --prep_def_merge_tr_red                 false
% 2.78/1.03  --prep_def_merge_tr_cl                  false
% 2.78/1.03  --smt_preprocessing                     true
% 2.78/1.03  --smt_ac_axioms                         fast
% 2.78/1.03  --preprocessed_out                      false
% 2.78/1.03  --preprocessed_stats                    false
% 2.78/1.03  
% 2.78/1.03  ------ Abstraction refinement Options
% 2.78/1.03  
% 2.78/1.03  --abstr_ref                             []
% 2.78/1.03  --abstr_ref_prep                        false
% 2.78/1.03  --abstr_ref_until_sat                   false
% 2.78/1.03  --abstr_ref_sig_restrict                funpre
% 2.78/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.78/1.03  --abstr_ref_under                       []
% 2.78/1.03  
% 2.78/1.03  ------ SAT Options
% 2.78/1.03  
% 2.78/1.03  --sat_mode                              false
% 2.78/1.03  --sat_fm_restart_options                ""
% 2.78/1.03  --sat_gr_def                            false
% 2.78/1.03  --sat_epr_types                         true
% 2.78/1.03  --sat_non_cyclic_types                  false
% 2.78/1.03  --sat_finite_models                     false
% 2.78/1.03  --sat_fm_lemmas                         false
% 2.78/1.03  --sat_fm_prep                           false
% 2.78/1.03  --sat_fm_uc_incr                        true
% 2.78/1.03  --sat_out_model                         small
% 2.78/1.03  --sat_out_clauses                       false
% 2.78/1.03  
% 2.78/1.03  ------ QBF Options
% 2.78/1.03  
% 2.78/1.03  --qbf_mode                              false
% 2.78/1.03  --qbf_elim_univ                         false
% 2.78/1.03  --qbf_dom_inst                          none
% 2.78/1.03  --qbf_dom_pre_inst                      false
% 2.78/1.03  --qbf_sk_in                             false
% 2.78/1.03  --qbf_pred_elim                         true
% 2.78/1.03  --qbf_split                             512
% 2.78/1.03  
% 2.78/1.03  ------ BMC1 Options
% 2.78/1.03  
% 2.78/1.03  --bmc1_incremental                      false
% 2.78/1.03  --bmc1_axioms                           reachable_all
% 2.78/1.03  --bmc1_min_bound                        0
% 2.78/1.03  --bmc1_max_bound                        -1
% 2.78/1.03  --bmc1_max_bound_default                -1
% 2.78/1.03  --bmc1_symbol_reachability              true
% 2.78/1.03  --bmc1_property_lemmas                  false
% 2.78/1.03  --bmc1_k_induction                      false
% 2.78/1.03  --bmc1_non_equiv_states                 false
% 2.78/1.03  --bmc1_deadlock                         false
% 2.78/1.03  --bmc1_ucm                              false
% 2.78/1.03  --bmc1_add_unsat_core                   none
% 2.78/1.03  --bmc1_unsat_core_children              false
% 2.78/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.78/1.03  --bmc1_out_stat                         full
% 2.78/1.03  --bmc1_ground_init                      false
% 2.78/1.03  --bmc1_pre_inst_next_state              false
% 2.78/1.03  --bmc1_pre_inst_state                   false
% 2.78/1.03  --bmc1_pre_inst_reach_state             false
% 2.78/1.03  --bmc1_out_unsat_core                   false
% 2.78/1.03  --bmc1_aig_witness_out                  false
% 2.78/1.03  --bmc1_verbose                          false
% 2.78/1.03  --bmc1_dump_clauses_tptp                false
% 2.78/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.78/1.03  --bmc1_dump_file                        -
% 2.78/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.78/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.78/1.03  --bmc1_ucm_extend_mode                  1
% 2.78/1.03  --bmc1_ucm_init_mode                    2
% 2.78/1.03  --bmc1_ucm_cone_mode                    none
% 2.78/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.78/1.03  --bmc1_ucm_relax_model                  4
% 2.78/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.78/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.78/1.03  --bmc1_ucm_layered_model                none
% 2.78/1.03  --bmc1_ucm_max_lemma_size               10
% 2.78/1.03  
% 2.78/1.03  ------ AIG Options
% 2.78/1.03  
% 2.78/1.03  --aig_mode                              false
% 2.78/1.03  
% 2.78/1.03  ------ Instantiation Options
% 2.78/1.03  
% 2.78/1.03  --instantiation_flag                    true
% 2.78/1.03  --inst_sos_flag                         false
% 2.78/1.03  --inst_sos_phase                        true
% 2.78/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.78/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.78/1.03  --inst_lit_sel_side                     num_symb
% 2.78/1.03  --inst_solver_per_active                1400
% 2.78/1.03  --inst_solver_calls_frac                1.
% 2.78/1.03  --inst_passive_queue_type               priority_queues
% 2.78/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.78/1.03  --inst_passive_queues_freq              [25;2]
% 2.78/1.03  --inst_dismatching                      true
% 2.78/1.03  --inst_eager_unprocessed_to_passive     true
% 2.78/1.03  --inst_prop_sim_given                   true
% 2.78/1.03  --inst_prop_sim_new                     false
% 2.78/1.03  --inst_subs_new                         false
% 2.78/1.03  --inst_eq_res_simp                      false
% 2.78/1.03  --inst_subs_given                       false
% 2.78/1.03  --inst_orphan_elimination               true
% 2.78/1.03  --inst_learning_loop_flag               true
% 2.78/1.03  --inst_learning_start                   3000
% 2.78/1.03  --inst_learning_factor                  2
% 2.78/1.03  --inst_start_prop_sim_after_learn       3
% 2.78/1.03  --inst_sel_renew                        solver
% 2.78/1.03  --inst_lit_activity_flag                true
% 2.78/1.03  --inst_restr_to_given                   false
% 2.78/1.03  --inst_activity_threshold               500
% 2.78/1.03  --inst_out_proof                        true
% 2.78/1.03  
% 2.78/1.03  ------ Resolution Options
% 2.78/1.03  
% 2.78/1.03  --resolution_flag                       true
% 2.78/1.03  --res_lit_sel                           adaptive
% 2.78/1.03  --res_lit_sel_side                      none
% 2.78/1.03  --res_ordering                          kbo
% 2.78/1.03  --res_to_prop_solver                    active
% 2.78/1.03  --res_prop_simpl_new                    false
% 2.78/1.03  --res_prop_simpl_given                  true
% 2.78/1.03  --res_passive_queue_type                priority_queues
% 2.78/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.78/1.03  --res_passive_queues_freq               [15;5]
% 2.78/1.03  --res_forward_subs                      full
% 2.78/1.03  --res_backward_subs                     full
% 2.78/1.03  --res_forward_subs_resolution           true
% 2.78/1.03  --res_backward_subs_resolution          true
% 2.78/1.03  --res_orphan_elimination                true
% 2.78/1.03  --res_time_limit                        2.
% 2.78/1.03  --res_out_proof                         true
% 2.78/1.03  
% 2.78/1.03  ------ Superposition Options
% 2.78/1.03  
% 2.78/1.03  --superposition_flag                    true
% 2.78/1.03  --sup_passive_queue_type                priority_queues
% 2.78/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.78/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.78/1.03  --demod_completeness_check              fast
% 2.78/1.03  --demod_use_ground                      true
% 2.78/1.03  --sup_to_prop_solver                    passive
% 2.78/1.03  --sup_prop_simpl_new                    true
% 2.78/1.03  --sup_prop_simpl_given                  true
% 2.78/1.03  --sup_fun_splitting                     false
% 2.78/1.03  --sup_smt_interval                      50000
% 2.78/1.03  
% 2.78/1.03  ------ Superposition Simplification Setup
% 2.78/1.03  
% 2.78/1.03  --sup_indices_passive                   []
% 2.78/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.78/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.03  --sup_full_bw                           [BwDemod]
% 2.78/1.03  --sup_immed_triv                        [TrivRules]
% 2.78/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.78/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.03  --sup_immed_bw_main                     []
% 2.78/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.78/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.03  
% 2.78/1.03  ------ Combination Options
% 2.78/1.03  
% 2.78/1.03  --comb_res_mult                         3
% 2.78/1.03  --comb_sup_mult                         2
% 2.78/1.03  --comb_inst_mult                        10
% 2.78/1.03  
% 2.78/1.03  ------ Debug Options
% 2.78/1.03  
% 2.78/1.03  --dbg_backtrace                         false
% 2.78/1.03  --dbg_dump_prop_clauses                 false
% 2.78/1.03  --dbg_dump_prop_clauses_file            -
% 2.78/1.03  --dbg_out_stat                          false
% 2.78/1.03  ------ Parsing...
% 2.78/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.78/1.03  
% 2.78/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.78/1.03  
% 2.78/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.78/1.03  
% 2.78/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.78/1.03  ------ Proving...
% 2.78/1.03  ------ Problem Properties 
% 2.78/1.03  
% 2.78/1.03  
% 2.78/1.03  clauses                                 22
% 2.78/1.03  conjectures                             3
% 2.78/1.03  EPR                                     0
% 2.78/1.03  Horn                                    16
% 2.78/1.03  unary                                   3
% 2.78/1.03  binary                                  1
% 2.78/1.03  lits                                    100
% 2.78/1.03  lits eq                                 12
% 2.78/1.03  fd_pure                                 0
% 2.78/1.03  fd_pseudo                               0
% 2.78/1.03  fd_cond                                 0
% 2.78/1.03  fd_pseudo_cond                          8
% 2.78/1.03  AC symbols                              0
% 2.78/1.03  
% 2.78/1.03  ------ Schedule dynamic 5 is on 
% 2.78/1.03  
% 2.78/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.78/1.03  
% 2.78/1.03  
% 2.78/1.03  ------ 
% 2.78/1.03  Current options:
% 2.78/1.03  ------ 
% 2.78/1.03  
% 2.78/1.03  ------ Input Options
% 2.78/1.03  
% 2.78/1.03  --out_options                           all
% 2.78/1.03  --tptp_safe_out                         true
% 2.78/1.03  --problem_path                          ""
% 2.78/1.03  --include_path                          ""
% 2.78/1.03  --clausifier                            res/vclausify_rel
% 2.78/1.03  --clausifier_options                    --mode clausify
% 2.78/1.03  --stdin                                 false
% 2.78/1.03  --stats_out                             all
% 2.78/1.03  
% 2.78/1.03  ------ General Options
% 2.78/1.03  
% 2.78/1.03  --fof                                   false
% 2.78/1.03  --time_out_real                         305.
% 2.78/1.03  --time_out_virtual                      -1.
% 2.78/1.03  --symbol_type_check                     false
% 2.78/1.03  --clausify_out                          false
% 2.78/1.03  --sig_cnt_out                           false
% 2.78/1.03  --trig_cnt_out                          false
% 2.78/1.03  --trig_cnt_out_tolerance                1.
% 2.78/1.03  --trig_cnt_out_sk_spl                   false
% 2.78/1.03  --abstr_cl_out                          false
% 2.78/1.03  
% 2.78/1.03  ------ Global Options
% 2.78/1.03  
% 2.78/1.03  --schedule                              default
% 2.78/1.03  --add_important_lit                     false
% 2.78/1.03  --prop_solver_per_cl                    1000
% 2.78/1.03  --min_unsat_core                        false
% 2.78/1.03  --soft_assumptions                      false
% 2.78/1.03  --soft_lemma_size                       3
% 2.78/1.03  --prop_impl_unit_size                   0
% 2.78/1.03  --prop_impl_unit                        []
% 2.78/1.03  --share_sel_clauses                     true
% 2.78/1.03  --reset_solvers                         false
% 2.78/1.03  --bc_imp_inh                            [conj_cone]
% 2.78/1.03  --conj_cone_tolerance                   3.
% 2.78/1.03  --extra_neg_conj                        none
% 2.78/1.03  --large_theory_mode                     true
% 2.78/1.03  --prolific_symb_bound                   200
% 2.78/1.03  --lt_threshold                          2000
% 2.78/1.03  --clause_weak_htbl                      true
% 2.78/1.03  --gc_record_bc_elim                     false
% 2.78/1.03  
% 2.78/1.03  ------ Preprocessing Options
% 2.78/1.03  
% 2.78/1.03  --preprocessing_flag                    true
% 2.78/1.03  --time_out_prep_mult                    0.1
% 2.78/1.03  --splitting_mode                        input
% 2.78/1.03  --splitting_grd                         true
% 2.78/1.03  --splitting_cvd                         false
% 2.78/1.03  --splitting_cvd_svl                     false
% 2.78/1.03  --splitting_nvd                         32
% 2.78/1.03  --sub_typing                            true
% 2.78/1.03  --prep_gs_sim                           true
% 2.78/1.03  --prep_unflatten                        true
% 2.78/1.03  --prep_res_sim                          true
% 2.78/1.03  --prep_upred                            true
% 2.78/1.03  --prep_sem_filter                       exhaustive
% 2.78/1.03  --prep_sem_filter_out                   false
% 2.78/1.03  --pred_elim                             true
% 2.78/1.03  --res_sim_input                         true
% 2.78/1.03  --eq_ax_congr_red                       true
% 2.78/1.03  --pure_diseq_elim                       true
% 2.78/1.03  --brand_transform                       false
% 2.78/1.03  --non_eq_to_eq                          false
% 2.78/1.03  --prep_def_merge                        true
% 2.78/1.03  --prep_def_merge_prop_impl              false
% 2.78/1.03  --prep_def_merge_mbd                    true
% 2.78/1.03  --prep_def_merge_tr_red                 false
% 2.78/1.03  --prep_def_merge_tr_cl                  false
% 2.78/1.03  --smt_preprocessing                     true
% 2.78/1.03  --smt_ac_axioms                         fast
% 2.78/1.03  --preprocessed_out                      false
% 2.78/1.03  --preprocessed_stats                    false
% 2.78/1.03  
% 2.78/1.03  ------ Abstraction refinement Options
% 2.78/1.03  
% 2.78/1.03  --abstr_ref                             []
% 2.78/1.03  --abstr_ref_prep                        false
% 2.78/1.03  --abstr_ref_until_sat                   false
% 2.78/1.03  --abstr_ref_sig_restrict                funpre
% 2.78/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.78/1.03  --abstr_ref_under                       []
% 2.78/1.03  
% 2.78/1.03  ------ SAT Options
% 2.78/1.03  
% 2.78/1.03  --sat_mode                              false
% 2.78/1.03  --sat_fm_restart_options                ""
% 2.78/1.03  --sat_gr_def                            false
% 2.78/1.03  --sat_epr_types                         true
% 2.78/1.03  --sat_non_cyclic_types                  false
% 2.78/1.03  --sat_finite_models                     false
% 2.78/1.03  --sat_fm_lemmas                         false
% 2.78/1.03  --sat_fm_prep                           false
% 2.78/1.03  --sat_fm_uc_incr                        true
% 2.78/1.03  --sat_out_model                         small
% 2.78/1.03  --sat_out_clauses                       false
% 2.78/1.03  
% 2.78/1.03  ------ QBF Options
% 2.78/1.03  
% 2.78/1.03  --qbf_mode                              false
% 2.78/1.03  --qbf_elim_univ                         false
% 2.78/1.03  --qbf_dom_inst                          none
% 2.78/1.03  --qbf_dom_pre_inst                      false
% 2.78/1.03  --qbf_sk_in                             false
% 2.78/1.03  --qbf_pred_elim                         true
% 2.78/1.03  --qbf_split                             512
% 2.78/1.03  
% 2.78/1.03  ------ BMC1 Options
% 2.78/1.03  
% 2.78/1.03  --bmc1_incremental                      false
% 2.78/1.03  --bmc1_axioms                           reachable_all
% 2.78/1.03  --bmc1_min_bound                        0
% 2.78/1.03  --bmc1_max_bound                        -1
% 2.78/1.03  --bmc1_max_bound_default                -1
% 2.78/1.03  --bmc1_symbol_reachability              true
% 2.78/1.03  --bmc1_property_lemmas                  false
% 2.78/1.03  --bmc1_k_induction                      false
% 2.78/1.03  --bmc1_non_equiv_states                 false
% 2.78/1.03  --bmc1_deadlock                         false
% 2.78/1.03  --bmc1_ucm                              false
% 2.78/1.03  --bmc1_add_unsat_core                   none
% 2.78/1.03  --bmc1_unsat_core_children              false
% 2.78/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.78/1.03  --bmc1_out_stat                         full
% 2.78/1.03  --bmc1_ground_init                      false
% 2.78/1.03  --bmc1_pre_inst_next_state              false
% 2.78/1.03  --bmc1_pre_inst_state                   false
% 2.78/1.03  --bmc1_pre_inst_reach_state             false
% 2.78/1.03  --bmc1_out_unsat_core                   false
% 2.78/1.03  --bmc1_aig_witness_out                  false
% 2.78/1.03  --bmc1_verbose                          false
% 2.78/1.03  --bmc1_dump_clauses_tptp                false
% 2.78/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.78/1.03  --bmc1_dump_file                        -
% 2.78/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.78/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.78/1.03  --bmc1_ucm_extend_mode                  1
% 2.78/1.03  --bmc1_ucm_init_mode                    2
% 2.78/1.03  --bmc1_ucm_cone_mode                    none
% 2.78/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.78/1.03  --bmc1_ucm_relax_model                  4
% 2.78/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.78/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.78/1.03  --bmc1_ucm_layered_model                none
% 2.78/1.03  --bmc1_ucm_max_lemma_size               10
% 2.78/1.03  
% 2.78/1.03  ------ AIG Options
% 2.78/1.03  
% 2.78/1.03  --aig_mode                              false
% 2.78/1.03  
% 2.78/1.03  ------ Instantiation Options
% 2.78/1.03  
% 2.78/1.03  --instantiation_flag                    true
% 2.78/1.03  --inst_sos_flag                         false
% 2.78/1.03  --inst_sos_phase                        true
% 2.78/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.78/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.78/1.03  --inst_lit_sel_side                     none
% 2.78/1.03  --inst_solver_per_active                1400
% 2.78/1.03  --inst_solver_calls_frac                1.
% 2.78/1.03  --inst_passive_queue_type               priority_queues
% 2.78/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.78/1.03  --inst_passive_queues_freq              [25;2]
% 2.78/1.03  --inst_dismatching                      true
% 2.78/1.03  --inst_eager_unprocessed_to_passive     true
% 2.78/1.03  --inst_prop_sim_given                   true
% 2.78/1.03  --inst_prop_sim_new                     false
% 2.78/1.03  --inst_subs_new                         false
% 2.78/1.03  --inst_eq_res_simp                      false
% 2.78/1.03  --inst_subs_given                       false
% 2.78/1.03  --inst_orphan_elimination               true
% 2.78/1.03  --inst_learning_loop_flag               true
% 2.78/1.03  --inst_learning_start                   3000
% 2.78/1.03  --inst_learning_factor                  2
% 2.78/1.03  --inst_start_prop_sim_after_learn       3
% 2.78/1.03  --inst_sel_renew                        solver
% 2.78/1.03  --inst_lit_activity_flag                true
% 2.78/1.03  --inst_restr_to_given                   false
% 2.78/1.03  --inst_activity_threshold               500
% 2.78/1.03  --inst_out_proof                        true
% 2.78/1.03  
% 2.78/1.03  ------ Resolution Options
% 2.78/1.03  
% 2.78/1.03  --resolution_flag                       false
% 2.78/1.03  --res_lit_sel                           adaptive
% 2.78/1.03  --res_lit_sel_side                      none
% 2.78/1.03  --res_ordering                          kbo
% 2.78/1.03  --res_to_prop_solver                    active
% 2.78/1.03  --res_prop_simpl_new                    false
% 2.78/1.03  --res_prop_simpl_given                  true
% 2.78/1.03  --res_passive_queue_type                priority_queues
% 2.78/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.78/1.03  --res_passive_queues_freq               [15;5]
% 2.78/1.03  --res_forward_subs                      full
% 2.78/1.03  --res_backward_subs                     full
% 2.78/1.03  --res_forward_subs_resolution           true
% 2.78/1.03  --res_backward_subs_resolution          true
% 2.78/1.03  --res_orphan_elimination                true
% 2.78/1.03  --res_time_limit                        2.
% 2.78/1.03  --res_out_proof                         true
% 2.78/1.03  
% 2.78/1.03  ------ Superposition Options
% 2.78/1.03  
% 2.78/1.03  --superposition_flag                    true
% 2.78/1.03  --sup_passive_queue_type                priority_queues
% 2.78/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.78/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.78/1.03  --demod_completeness_check              fast
% 2.78/1.03  --demod_use_ground                      true
% 2.78/1.03  --sup_to_prop_solver                    passive
% 2.78/1.03  --sup_prop_simpl_new                    true
% 2.78/1.03  --sup_prop_simpl_given                  true
% 2.78/1.03  --sup_fun_splitting                     false
% 2.78/1.03  --sup_smt_interval                      50000
% 2.78/1.03  
% 2.78/1.03  ------ Superposition Simplification Setup
% 2.78/1.03  
% 2.78/1.03  --sup_indices_passive                   []
% 2.78/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.78/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.03  --sup_full_bw                           [BwDemod]
% 2.78/1.03  --sup_immed_triv                        [TrivRules]
% 2.78/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.78/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.03  --sup_immed_bw_main                     []
% 2.78/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.78/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.03  
% 2.78/1.03  ------ Combination Options
% 2.78/1.03  
% 2.78/1.03  --comb_res_mult                         3
% 2.78/1.03  --comb_sup_mult                         2
% 2.78/1.03  --comb_inst_mult                        10
% 2.78/1.03  
% 2.78/1.03  ------ Debug Options
% 2.78/1.03  
% 2.78/1.03  --dbg_backtrace                         false
% 2.78/1.03  --dbg_dump_prop_clauses                 false
% 2.78/1.03  --dbg_dump_prop_clauses_file            -
% 2.78/1.03  --dbg_out_stat                          false
% 2.78/1.03  
% 2.78/1.03  
% 2.78/1.03  
% 2.78/1.03  
% 2.78/1.03  ------ Proving...
% 2.78/1.03  
% 2.78/1.03  
% 2.78/1.03  % SZS status Theorem for theBenchmark.p
% 2.78/1.03  
% 2.78/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.78/1.03  
% 2.78/1.03  fof(f6,axiom,(
% 2.78/1.03    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 2.78/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/1.04  
% 2.78/1.04  fof(f21,plain,(
% 2.78/1.04    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 2.78/1.04    inference(ennf_transformation,[],[f6])).
% 2.78/1.04  
% 2.78/1.04  fof(f22,plain,(
% 2.78/1.04    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.78/1.04    inference(flattening,[],[f21])).
% 2.78/1.04  
% 2.78/1.04  fof(f34,plain,(
% 2.78/1.04    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.78/1.04    inference(nnf_transformation,[],[f22])).
% 2.78/1.04  
% 2.78/1.04  fof(f35,plain,(
% 2.78/1.04    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.78/1.04    inference(flattening,[],[f34])).
% 2.78/1.04  
% 2.78/1.04  fof(f36,plain,(
% 2.78/1.04    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.78/1.04    inference(rectify,[],[f35])).
% 2.78/1.04  
% 2.78/1.04  fof(f37,plain,(
% 2.78/1.04    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK1(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X1) & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0))))),
% 2.78/1.04    introduced(choice_axiom,[])).
% 2.78/1.04  
% 2.78/1.04  fof(f38,plain,(
% 2.78/1.04    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,sK1(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK1(X0,X1,X2,X3),X1) & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.78/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f37])).
% 2.78/1.04  
% 2.78/1.04  fof(f60,plain,(
% 2.78/1.04    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,sK1(X0,X1,X2,X3),X3) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.78/1.04    inference(cnf_transformation,[],[f38])).
% 2.78/1.04  
% 2.78/1.04  fof(f2,axiom,(
% 2.78/1.04    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 2.78/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/1.04  
% 2.78/1.04  fof(f13,plain,(
% 2.78/1.04    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 2.78/1.04    inference(ennf_transformation,[],[f2])).
% 2.78/1.04  
% 2.78/1.04  fof(f14,plain,(
% 2.78/1.04    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 2.78/1.04    inference(flattening,[],[f13])).
% 2.78/1.04  
% 2.78/1.04  fof(f44,plain,(
% 2.78/1.04    ( ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0)) )),
% 2.78/1.04    inference(cnf_transformation,[],[f14])).
% 2.78/1.04  
% 2.78/1.04  fof(f9,conjecture,(
% 2.78/1.04    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1)))),
% 2.78/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/1.04  
% 2.78/1.04  fof(f10,negated_conjecture,(
% 2.78/1.04    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1)))),
% 2.78/1.04    inference(negated_conjecture,[],[f9])).
% 2.78/1.04  
% 2.78/1.04  fof(f27,plain,(
% 2.78/1.04    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)))),
% 2.78/1.04    inference(ennf_transformation,[],[f10])).
% 2.78/1.04  
% 2.78/1.04  fof(f28,plain,(
% 2.78/1.04    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 2.78/1.04    inference(flattening,[],[f27])).
% 2.78/1.04  
% 2.78/1.04  fof(f41,plain,(
% 2.78/1.04    ( ! [X0,X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) => (k12_lattice3(X0,X1,k13_lattice3(X0,X1,sK4)) != X1 & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 2.78/1.04    introduced(choice_axiom,[])).
% 2.78/1.04  
% 2.78/1.04  fof(f40,plain,(
% 2.78/1.04    ( ! [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k12_lattice3(X0,sK3,k13_lattice3(X0,sK3,X2)) != sK3 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 2.78/1.04    introduced(choice_axiom,[])).
% 2.78/1.04  
% 2.78/1.04  fof(f39,plain,(
% 2.78/1.04    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => (? [X1] : (? [X2] : (k12_lattice3(sK2,X1,k13_lattice3(sK2,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_orders_2(sK2) & v2_lattice3(sK2) & v1_lattice3(sK2) & v5_orders_2(sK2) & v3_orders_2(sK2))),
% 2.78/1.04    introduced(choice_axiom,[])).
% 2.78/1.04  
% 2.78/1.04  fof(f42,plain,(
% 2.78/1.04    ((k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 & m1_subset_1(sK4,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_orders_2(sK2) & v2_lattice3(sK2) & v1_lattice3(sK2) & v5_orders_2(sK2) & v3_orders_2(sK2)),
% 2.78/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f28,f41,f40,f39])).
% 2.78/1.04  
% 2.78/1.04  fof(f66,plain,(
% 2.78/1.04    v2_lattice3(sK2)),
% 2.78/1.04    inference(cnf_transformation,[],[f42])).
% 2.78/1.04  
% 2.78/1.04  fof(f64,plain,(
% 2.78/1.04    v5_orders_2(sK2)),
% 2.78/1.04    inference(cnf_transformation,[],[f42])).
% 2.78/1.04  
% 2.78/1.04  fof(f67,plain,(
% 2.78/1.04    l1_orders_2(sK2)),
% 2.78/1.04    inference(cnf_transformation,[],[f42])).
% 2.78/1.04  
% 2.78/1.04  fof(f58,plain,(
% 2.78/1.04    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | r1_orders_2(X0,sK1(X0,X1,X2,X3),X1) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.78/1.04    inference(cnf_transformation,[],[f38])).
% 2.78/1.04  
% 2.78/1.04  fof(f4,axiom,(
% 2.78/1.04    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 2.78/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/1.04  
% 2.78/1.04  fof(f17,plain,(
% 2.78/1.04    ! [X0,X1,X2] : (m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 2.78/1.04    inference(ennf_transformation,[],[f4])).
% 2.78/1.04  
% 2.78/1.04  fof(f18,plain,(
% 2.78/1.04    ! [X0,X1,X2] : (m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 2.78/1.04    inference(flattening,[],[f17])).
% 2.78/1.04  
% 2.78/1.04  fof(f46,plain,(
% 2.78/1.04    ( ! [X2,X0,X1] : (m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.78/1.04    inference(cnf_transformation,[],[f18])).
% 2.78/1.04  
% 2.78/1.04  fof(f5,axiom,(
% 2.78/1.04    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 2.78/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/1.04  
% 2.78/1.04  fof(f19,plain,(
% 2.78/1.04    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 2.78/1.04    inference(ennf_transformation,[],[f5])).
% 2.78/1.04  
% 2.78/1.04  fof(f20,plain,(
% 2.78/1.04    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.78/1.04    inference(flattening,[],[f19])).
% 2.78/1.04  
% 2.78/1.04  fof(f29,plain,(
% 2.78/1.04    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3))) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.78/1.04    inference(nnf_transformation,[],[f20])).
% 2.78/1.04  
% 2.78/1.04  fof(f30,plain,(
% 2.78/1.04    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.78/1.04    inference(flattening,[],[f29])).
% 2.78/1.04  
% 2.78/1.04  fof(f31,plain,(
% 2.78/1.04    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.78/1.04    inference(rectify,[],[f30])).
% 2.78/1.04  
% 2.78/1.04  fof(f32,plain,(
% 2.78/1.04    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,X3,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))))),
% 2.78/1.04    introduced(choice_axiom,[])).
% 2.78/1.04  
% 2.78/1.04  fof(f33,plain,(
% 2.78/1.04    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,X3,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.78/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 2.78/1.04  
% 2.78/1.04  fof(f47,plain,(
% 2.78/1.04    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X1,X3) | k10_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.78/1.04    inference(cnf_transformation,[],[f33])).
% 2.78/1.04  
% 2.78/1.04  fof(f73,plain,(
% 2.78/1.04    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.78/1.04    inference(equality_resolution,[],[f47])).
% 2.78/1.04  
% 2.78/1.04  fof(f65,plain,(
% 2.78/1.04    v1_lattice3(sK2)),
% 2.78/1.04    inference(cnf_transformation,[],[f42])).
% 2.78/1.04  
% 2.78/1.04  fof(f7,axiom,(
% 2.78/1.04    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2))),
% 2.78/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/1.04  
% 2.78/1.04  fof(f23,plain,(
% 2.78/1.04    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 2.78/1.04    inference(ennf_transformation,[],[f7])).
% 2.78/1.04  
% 2.78/1.04  fof(f24,plain,(
% 2.78/1.04    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 2.78/1.04    inference(flattening,[],[f23])).
% 2.78/1.04  
% 2.78/1.04  fof(f61,plain,(
% 2.78/1.04    ( ! [X2,X0,X1] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 2.78/1.04    inference(cnf_transformation,[],[f24])).
% 2.78/1.04  
% 2.78/1.04  fof(f8,axiom,(
% 2.78/1.04    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2))),
% 2.78/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/1.04  
% 2.78/1.04  fof(f25,plain,(
% 2.78/1.04    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 2.78/1.04    inference(ennf_transformation,[],[f8])).
% 2.78/1.04  
% 2.78/1.04  fof(f26,plain,(
% 2.78/1.04    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 2.78/1.04    inference(flattening,[],[f25])).
% 2.78/1.04  
% 2.78/1.04  fof(f62,plain,(
% 2.78/1.04    ( ! [X2,X0,X1] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 2.78/1.04    inference(cnf_transformation,[],[f26])).
% 2.78/1.04  
% 2.78/1.04  fof(f1,axiom,(
% 2.78/1.04    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 2.78/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/1.04  
% 2.78/1.04  fof(f11,plain,(
% 2.78/1.04    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.78/1.04    inference(ennf_transformation,[],[f1])).
% 2.78/1.04  
% 2.78/1.04  fof(f12,plain,(
% 2.78/1.04    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.78/1.04    inference(flattening,[],[f11])).
% 2.78/1.04  
% 2.78/1.04  fof(f43,plain,(
% 2.78/1.04    ( ! [X0,X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.78/1.04    inference(cnf_transformation,[],[f12])).
% 2.78/1.04  
% 2.78/1.04  fof(f63,plain,(
% 2.78/1.04    v3_orders_2(sK2)),
% 2.78/1.04    inference(cnf_transformation,[],[f42])).
% 2.78/1.04  
% 2.78/1.04  fof(f70,plain,(
% 2.78/1.04    k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3),
% 2.78/1.04    inference(cnf_transformation,[],[f42])).
% 2.78/1.04  
% 2.78/1.04  fof(f69,plain,(
% 2.78/1.04    m1_subset_1(sK4,u1_struct_0(sK2))),
% 2.78/1.04    inference(cnf_transformation,[],[f42])).
% 2.78/1.04  
% 2.78/1.04  fof(f68,plain,(
% 2.78/1.04    m1_subset_1(sK3,u1_struct_0(sK2))),
% 2.78/1.04    inference(cnf_transformation,[],[f42])).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1138,plain,
% 2.78/1.04      ( X0_47 != X1_47 | X2_47 != X1_47 | X2_47 = X0_47 ),
% 2.78/1.04      theory(equality) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_4743,plain,
% 2.78/1.04      ( X0_47 != X1_47
% 2.78/1.04      | X0_47 = k11_lattice3(sK2,X2_47,k10_lattice3(sK2,sK3,sK4))
% 2.78/1.04      | k11_lattice3(sK2,X2_47,k10_lattice3(sK2,sK3,sK4)) != X1_47 ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_1138]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_4744,plain,
% 2.78/1.04      ( k11_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,sK4)) != sK3
% 2.78/1.04      | sK3 = k11_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,sK4))
% 2.78/1.04      | sK3 != sK3 ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_4743]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_11,plain,
% 2.78/1.04      ( ~ r1_orders_2(X0,X1,X2)
% 2.78/1.04      | ~ r1_orders_2(X0,X1,X3)
% 2.78/1.04      | ~ r1_orders_2(X0,sK1(X0,X3,X2,X1),X1)
% 2.78/1.04      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.78/1.04      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.78/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.78/1.04      | ~ v5_orders_2(X0)
% 2.78/1.04      | ~ v2_lattice3(X0)
% 2.78/1.04      | v2_struct_0(X0)
% 2.78/1.04      | ~ l1_orders_2(X0)
% 2.78/1.04      | k11_lattice3(X0,X3,X2) = X1 ),
% 2.78/1.04      inference(cnf_transformation,[],[f60]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1,plain,
% 2.78/1.04      ( ~ v2_lattice3(X0) | ~ v2_struct_0(X0) | ~ l1_orders_2(X0) ),
% 2.78/1.04      inference(cnf_transformation,[],[f44]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_189,plain,
% 2.78/1.04      ( ~ v2_lattice3(X0)
% 2.78/1.04      | ~ v5_orders_2(X0)
% 2.78/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.78/1.04      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.78/1.04      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.78/1.04      | ~ r1_orders_2(X0,sK1(X0,X3,X2,X1),X1)
% 2.78/1.04      | ~ r1_orders_2(X0,X1,X3)
% 2.78/1.04      | ~ r1_orders_2(X0,X1,X2)
% 2.78/1.04      | ~ l1_orders_2(X0)
% 2.78/1.04      | k11_lattice3(X0,X3,X2) = X1 ),
% 2.78/1.04      inference(global_propositional_subsumption,
% 2.78/1.04                [status(thm)],
% 2.78/1.04                [c_11,c_1]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_190,plain,
% 2.78/1.04      ( ~ r1_orders_2(X0,X1,X2)
% 2.78/1.04      | ~ r1_orders_2(X0,X1,X3)
% 2.78/1.04      | ~ r1_orders_2(X0,sK1(X0,X2,X3,X1),X1)
% 2.78/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.78/1.04      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.78/1.04      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.78/1.04      | ~ v5_orders_2(X0)
% 2.78/1.04      | ~ v2_lattice3(X0)
% 2.78/1.04      | ~ l1_orders_2(X0)
% 2.78/1.04      | k11_lattice3(X0,X2,X3) = X1 ),
% 2.78/1.04      inference(renaming,[status(thm)],[c_189]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_24,negated_conjecture,
% 2.78/1.04      ( v2_lattice3(sK2) ),
% 2.78/1.04      inference(cnf_transformation,[],[f66]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_348,plain,
% 2.78/1.04      ( ~ r1_orders_2(X0,X1,X2)
% 2.78/1.04      | ~ r1_orders_2(X0,X1,X3)
% 2.78/1.04      | ~ r1_orders_2(X0,sK1(X0,X3,X2,X1),X1)
% 2.78/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.78/1.04      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.78/1.04      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.78/1.04      | ~ v5_orders_2(X0)
% 2.78/1.04      | ~ l1_orders_2(X0)
% 2.78/1.04      | k11_lattice3(X0,X3,X2) = X1
% 2.78/1.04      | sK2 != X0 ),
% 2.78/1.04      inference(resolution_lifted,[status(thm)],[c_190,c_24]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_349,plain,
% 2.78/1.04      ( ~ r1_orders_2(sK2,X0,X1)
% 2.78/1.04      | ~ r1_orders_2(sK2,X0,X2)
% 2.78/1.04      | ~ r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X0)
% 2.78/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.78/1.04      | ~ v5_orders_2(sK2)
% 2.78/1.04      | ~ l1_orders_2(sK2)
% 2.78/1.04      | k11_lattice3(sK2,X1,X2) = X0 ),
% 2.78/1.04      inference(unflattening,[status(thm)],[c_348]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_26,negated_conjecture,
% 2.78/1.04      ( v5_orders_2(sK2) ),
% 2.78/1.04      inference(cnf_transformation,[],[f64]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_23,negated_conjecture,
% 2.78/1.04      ( l1_orders_2(sK2) ),
% 2.78/1.04      inference(cnf_transformation,[],[f67]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_353,plain,
% 2.78/1.04      ( ~ r1_orders_2(sK2,X0,X1)
% 2.78/1.04      | ~ r1_orders_2(sK2,X0,X2)
% 2.78/1.04      | ~ r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X0)
% 2.78/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.78/1.04      | k11_lattice3(sK2,X1,X2) = X0 ),
% 2.78/1.04      inference(global_propositional_subsumption,
% 2.78/1.04                [status(thm)],
% 2.78/1.04                [c_349,c_26,c_23]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_354,plain,
% 2.78/1.04      ( ~ r1_orders_2(sK2,X0,X1)
% 2.78/1.04      | ~ r1_orders_2(sK2,X0,X2)
% 2.78/1.04      | ~ r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X0)
% 2.78/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 2.78/1.04      | k11_lattice3(sK2,X1,X2) = X0 ),
% 2.78/1.04      inference(renaming,[status(thm)],[c_353]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1131,plain,
% 2.78/1.04      ( ~ r1_orders_2(sK2,X0_47,X1_47)
% 2.78/1.04      | ~ r1_orders_2(sK2,X0_47,X2_47)
% 2.78/1.04      | ~ r1_orders_2(sK2,sK1(sK2,X1_47,X2_47,X0_47),X0_47)
% 2.78/1.04      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(X2_47,u1_struct_0(sK2))
% 2.78/1.04      | k11_lattice3(sK2,X1_47,X2_47) = X0_47 ),
% 2.78/1.04      inference(subtyping,[status(esa)],[c_354]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_4513,plain,
% 2.78/1.04      ( ~ r1_orders_2(sK2,sK1(sK2,X0_47,k10_lattice3(sK2,sK3,sK4),sK3),sK3)
% 2.78/1.04      | ~ r1_orders_2(sK2,sK3,X0_47)
% 2.78/1.04      | ~ r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK4))
% 2.78/1.04      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(k10_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.78/1.04      | k11_lattice3(sK2,X0_47,k10_lattice3(sK2,sK3,sK4)) = sK3 ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_1131]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_4530,plain,
% 2.78/1.04      ( ~ r1_orders_2(sK2,sK1(sK2,sK3,k10_lattice3(sK2,sK3,sK4),sK3),sK3)
% 2.78/1.04      | ~ r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK4))
% 2.78/1.04      | ~ r1_orders_2(sK2,sK3,sK3)
% 2.78/1.04      | ~ m1_subset_1(k10_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.78/1.04      | k11_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,sK4)) = sK3 ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_4513]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_13,plain,
% 2.78/1.04      ( ~ r1_orders_2(X0,X1,X2)
% 2.78/1.04      | ~ r1_orders_2(X0,X1,X3)
% 2.78/1.04      | r1_orders_2(X0,sK1(X0,X3,X2,X1),X3)
% 2.78/1.04      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.78/1.04      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.78/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.78/1.04      | ~ v5_orders_2(X0)
% 2.78/1.04      | ~ v2_lattice3(X0)
% 2.78/1.04      | v2_struct_0(X0)
% 2.78/1.04      | ~ l1_orders_2(X0)
% 2.78/1.04      | k11_lattice3(X0,X3,X2) = X1 ),
% 2.78/1.04      inference(cnf_transformation,[],[f58]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_177,plain,
% 2.78/1.04      ( ~ v2_lattice3(X0)
% 2.78/1.04      | ~ v5_orders_2(X0)
% 2.78/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.78/1.04      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.78/1.04      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.78/1.04      | r1_orders_2(X0,sK1(X0,X3,X2,X1),X3)
% 2.78/1.04      | ~ r1_orders_2(X0,X1,X3)
% 2.78/1.04      | ~ r1_orders_2(X0,X1,X2)
% 2.78/1.04      | ~ l1_orders_2(X0)
% 2.78/1.04      | k11_lattice3(X0,X3,X2) = X1 ),
% 2.78/1.04      inference(global_propositional_subsumption,
% 2.78/1.04                [status(thm)],
% 2.78/1.04                [c_13,c_1]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_178,plain,
% 2.78/1.04      ( ~ r1_orders_2(X0,X1,X2)
% 2.78/1.04      | ~ r1_orders_2(X0,X1,X3)
% 2.78/1.04      | r1_orders_2(X0,sK1(X0,X2,X3,X1),X2)
% 2.78/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.78/1.04      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.78/1.04      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.78/1.04      | ~ v5_orders_2(X0)
% 2.78/1.04      | ~ v2_lattice3(X0)
% 2.78/1.04      | ~ l1_orders_2(X0)
% 2.78/1.04      | k11_lattice3(X0,X2,X3) = X1 ),
% 2.78/1.04      inference(renaming,[status(thm)],[c_177]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_414,plain,
% 2.78/1.04      ( ~ r1_orders_2(X0,X1,X2)
% 2.78/1.04      | ~ r1_orders_2(X0,X1,X3)
% 2.78/1.04      | r1_orders_2(X0,sK1(X0,X3,X2,X1),X3)
% 2.78/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.78/1.04      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.78/1.04      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.78/1.04      | ~ v5_orders_2(X0)
% 2.78/1.04      | ~ l1_orders_2(X0)
% 2.78/1.04      | k11_lattice3(X0,X3,X2) = X1
% 2.78/1.04      | sK2 != X0 ),
% 2.78/1.04      inference(resolution_lifted,[status(thm)],[c_178,c_24]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_415,plain,
% 2.78/1.04      ( ~ r1_orders_2(sK2,X0,X1)
% 2.78/1.04      | ~ r1_orders_2(sK2,X0,X2)
% 2.78/1.04      | r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X1)
% 2.78/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.78/1.04      | ~ v5_orders_2(sK2)
% 2.78/1.04      | ~ l1_orders_2(sK2)
% 2.78/1.04      | k11_lattice3(sK2,X1,X2) = X0 ),
% 2.78/1.04      inference(unflattening,[status(thm)],[c_414]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_417,plain,
% 2.78/1.04      ( ~ r1_orders_2(sK2,X0,X1)
% 2.78/1.04      | ~ r1_orders_2(sK2,X0,X2)
% 2.78/1.04      | r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X1)
% 2.78/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.78/1.04      | k11_lattice3(sK2,X1,X2) = X0 ),
% 2.78/1.04      inference(global_propositional_subsumption,
% 2.78/1.04                [status(thm)],
% 2.78/1.04                [c_415,c_26,c_23]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_418,plain,
% 2.78/1.04      ( ~ r1_orders_2(sK2,X0,X1)
% 2.78/1.04      | ~ r1_orders_2(sK2,X0,X2)
% 2.78/1.04      | r1_orders_2(sK2,sK1(sK2,X1,X2,X0),X1)
% 2.78/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 2.78/1.04      | k11_lattice3(sK2,X1,X2) = X0 ),
% 2.78/1.04      inference(renaming,[status(thm)],[c_417]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1129,plain,
% 2.78/1.04      ( ~ r1_orders_2(sK2,X0_47,X1_47)
% 2.78/1.04      | ~ r1_orders_2(sK2,X0_47,X2_47)
% 2.78/1.04      | r1_orders_2(sK2,sK1(sK2,X1_47,X2_47,X0_47),X1_47)
% 2.78/1.04      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(X2_47,u1_struct_0(sK2))
% 2.78/1.04      | k11_lattice3(sK2,X1_47,X2_47) = X0_47 ),
% 2.78/1.04      inference(subtyping,[status(esa)],[c_418]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_4515,plain,
% 2.78/1.04      ( r1_orders_2(sK2,sK1(sK2,X0_47,k10_lattice3(sK2,sK3,sK4),sK3),X0_47)
% 2.78/1.04      | ~ r1_orders_2(sK2,sK3,X0_47)
% 2.78/1.04      | ~ r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK4))
% 2.78/1.04      | ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(k10_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.78/1.04      | k11_lattice3(sK2,X0_47,k10_lattice3(sK2,sK3,sK4)) = sK3 ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_1129]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_4522,plain,
% 2.78/1.04      ( r1_orders_2(sK2,sK1(sK2,sK3,k10_lattice3(sK2,sK3,sK4),sK3),sK3)
% 2.78/1.04      | ~ r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK4))
% 2.78/1.04      | ~ r1_orders_2(sK2,sK3,sK3)
% 2.78/1.04      | ~ m1_subset_1(k10_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.78/1.04      | k11_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,sK4)) = sK3 ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_4515]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_3,plain,
% 2.78/1.04      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.78/1.04      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.78/1.04      | m1_subset_1(k10_lattice3(X1,X0,X2),u1_struct_0(X1))
% 2.78/1.04      | ~ l1_orders_2(X1) ),
% 2.78/1.04      inference(cnf_transformation,[],[f46]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_946,plain,
% 2.78/1.04      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.78/1.04      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.78/1.04      | m1_subset_1(k10_lattice3(X1,X0,X2),u1_struct_0(X1))
% 2.78/1.04      | sK2 != X1 ),
% 2.78/1.04      inference(resolution_lifted,[status(thm)],[c_3,c_23]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_947,plain,
% 2.78/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.78/1.04      | m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
% 2.78/1.04      inference(unflattening,[status(thm)],[c_946]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_10,plain,
% 2.78/1.04      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 2.78/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.78/1.04      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.78/1.04      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.78/1.04      | ~ v1_lattice3(X0)
% 2.78/1.04      | ~ v5_orders_2(X0)
% 2.78/1.04      | v2_struct_0(X0)
% 2.78/1.04      | ~ l1_orders_2(X0) ),
% 2.78/1.04      inference(cnf_transformation,[],[f73]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_553,plain,
% 2.78/1.04      ( ~ v2_struct_0(X0) | ~ l1_orders_2(X0) | sK2 != X0 ),
% 2.78/1.04      inference(resolution_lifted,[status(thm)],[c_1,c_24]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_554,plain,
% 2.78/1.04      ( ~ v2_struct_0(sK2) | ~ l1_orders_2(sK2) ),
% 2.78/1.04      inference(unflattening,[status(thm)],[c_553]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_82,plain,
% 2.78/1.04      ( ~ v2_lattice3(sK2) | ~ v2_struct_0(sK2) | ~ l1_orders_2(sK2) ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_1]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_556,plain,
% 2.78/1.04      ( ~ v2_struct_0(sK2) ),
% 2.78/1.04      inference(global_propositional_subsumption,
% 2.78/1.04                [status(thm)],
% 2.78/1.04                [c_554,c_24,c_23,c_82]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_666,plain,
% 2.78/1.04      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 2.78/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.78/1.04      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.78/1.04      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.78/1.04      | ~ v1_lattice3(X0)
% 2.78/1.04      | ~ v5_orders_2(X0)
% 2.78/1.04      | ~ l1_orders_2(X0)
% 2.78/1.04      | sK2 != X0 ),
% 2.78/1.04      inference(resolution_lifted,[status(thm)],[c_10,c_556]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_667,plain,
% 2.78/1.04      ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
% 2.78/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2))
% 2.78/1.04      | ~ v1_lattice3(sK2)
% 2.78/1.04      | ~ v5_orders_2(sK2)
% 2.78/1.04      | ~ l1_orders_2(sK2) ),
% 2.78/1.04      inference(unflattening,[status(thm)],[c_666]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_25,negated_conjecture,
% 2.78/1.04      ( v1_lattice3(sK2) ),
% 2.78/1.04      inference(cnf_transformation,[],[f65]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_671,plain,
% 2.78/1.04      ( ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.78/1.04      | r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1)) ),
% 2.78/1.04      inference(global_propositional_subsumption,
% 2.78/1.04                [status(thm)],
% 2.78/1.04                [c_667,c_26,c_25,c_23]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_672,plain,
% 2.78/1.04      ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
% 2.78/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(k10_lattice3(sK2,X0,X1),u1_struct_0(sK2)) ),
% 2.78/1.04      inference(renaming,[status(thm)],[c_671]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_965,plain,
% 2.78/1.04      ( r1_orders_2(sK2,X0,k10_lattice3(sK2,X0,X1))
% 2.78/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 2.78/1.04      inference(backward_subsumption_resolution,
% 2.78/1.04                [status(thm)],
% 2.78/1.04                [c_947,c_672]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1115,plain,
% 2.78/1.04      ( r1_orders_2(sK2,X0_47,k10_lattice3(sK2,X0_47,X1_47))
% 2.78/1.04      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(X0_47,u1_struct_0(sK2)) ),
% 2.78/1.04      inference(subtyping,[status(esa)],[c_965]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_2645,plain,
% 2.78/1.04      ( r1_orders_2(sK2,sK3,k10_lattice3(sK2,sK3,sK4))
% 2.78/1.04      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_1115]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1934,plain,
% 2.78/1.04      ( X0_47 != X1_47
% 2.78/1.04      | k12_lattice3(sK2,X2_47,X3_47) != X1_47
% 2.78/1.04      | k12_lattice3(sK2,X2_47,X3_47) = X0_47 ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_1138]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_2521,plain,
% 2.78/1.04      ( X0_47 != k11_lattice3(sK2,X1_47,k10_lattice3(sK2,sK3,sK4))
% 2.78/1.04      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_47
% 2.78/1.04      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k11_lattice3(sK2,X1_47,k10_lattice3(sK2,sK3,sK4)) ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_1934]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_2522,plain,
% 2.78/1.04      ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k11_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,sK4))
% 2.78/1.04      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = sK3
% 2.78/1.04      | sK3 != k11_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,sK4)) ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_2521]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_18,plain,
% 2.78/1.04      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.78/1.04      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.78/1.04      | ~ v5_orders_2(X1)
% 2.78/1.04      | ~ v2_lattice3(X1)
% 2.78/1.04      | ~ l1_orders_2(X1)
% 2.78/1.04      | k11_lattice3(X1,X0,X2) = k12_lattice3(X1,X0,X2) ),
% 2.78/1.04      inference(cnf_transformation,[],[f61]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_564,plain,
% 2.78/1.04      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.78/1.04      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.78/1.04      | ~ v5_orders_2(X1)
% 2.78/1.04      | ~ l1_orders_2(X1)
% 2.78/1.04      | k11_lattice3(X1,X0,X2) = k12_lattice3(X1,X0,X2)
% 2.78/1.04      | sK2 != X1 ),
% 2.78/1.04      inference(resolution_lifted,[status(thm)],[c_18,c_24]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_565,plain,
% 2.78/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.78/1.04      | ~ v5_orders_2(sK2)
% 2.78/1.04      | ~ l1_orders_2(sK2)
% 2.78/1.04      | k11_lattice3(sK2,X0,X1) = k12_lattice3(sK2,X0,X1) ),
% 2.78/1.04      inference(unflattening,[status(thm)],[c_564]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_569,plain,
% 2.78/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.78/1.04      | k11_lattice3(sK2,X0,X1) = k12_lattice3(sK2,X0,X1) ),
% 2.78/1.04      inference(global_propositional_subsumption,
% 2.78/1.04                [status(thm)],
% 2.78/1.04                [c_565,c_26,c_23]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_570,plain,
% 2.78/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.78/1.04      | k11_lattice3(sK2,X1,X0) = k12_lattice3(sK2,X1,X0) ),
% 2.78/1.04      inference(renaming,[status(thm)],[c_569]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1124,plain,
% 2.78/1.04      ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 2.78/1.04      | k11_lattice3(sK2,X1_47,X0_47) = k12_lattice3(sK2,X1_47,X0_47) ),
% 2.78/1.04      inference(subtyping,[status(esa)],[c_570]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_2160,plain,
% 2.78/1.04      ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(k10_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 2.78/1.04      | k11_lattice3(sK2,X0_47,k10_lattice3(sK2,sK3,sK4)) = k12_lattice3(sK2,X0_47,k10_lattice3(sK2,sK3,sK4)) ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_1124]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_2163,plain,
% 2.78/1.04      ( ~ m1_subset_1(k10_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.78/1.04      | k11_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,sK4)) = k12_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,sK4)) ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_2160]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1798,plain,
% 2.78/1.04      ( X0_47 != X1_47
% 2.78/1.04      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != X1_47
% 2.78/1.04      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_47 ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_1138]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1908,plain,
% 2.78/1.04      ( X0_47 != k12_lattice3(sK2,X1_47,k10_lattice3(sK2,sK3,sK4))
% 2.78/1.04      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = X0_47
% 2.78/1.04      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k12_lattice3(sK2,X1_47,k10_lattice3(sK2,sK3,sK4)) ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_1798]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_2159,plain,
% 2.78/1.04      ( k11_lattice3(sK2,X0_47,k10_lattice3(sK2,sK3,sK4)) != k12_lattice3(sK2,X0_47,k10_lattice3(sK2,sK3,sK4))
% 2.78/1.04      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = k11_lattice3(sK2,X0_47,k10_lattice3(sK2,sK3,sK4))
% 2.78/1.04      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k12_lattice3(sK2,X0_47,k10_lattice3(sK2,sK3,sK4)) ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_1908]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_2161,plain,
% 2.78/1.04      ( k11_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,sK4)) != k12_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,sK4))
% 2.78/1.04      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = k11_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,sK4))
% 2.78/1.04      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != k12_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,sK4)) ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_2159]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1117,plain,
% 2.78/1.04      ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 2.78/1.04      | m1_subset_1(k10_lattice3(sK2,X0_47,X1_47),u1_struct_0(sK2)) ),
% 2.78/1.04      inference(subtyping,[status(esa)],[c_947]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_2083,plain,
% 2.78/1.04      ( m1_subset_1(k10_lattice3(sK2,sK3,sK4),u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_1117]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_19,plain,
% 2.78/1.04      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.78/1.04      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.78/1.04      | ~ v1_lattice3(X1)
% 2.78/1.04      | ~ v5_orders_2(X1)
% 2.78/1.04      | ~ l1_orders_2(X1)
% 2.78/1.04      | k13_lattice3(X1,X0,X2) = k10_lattice3(X1,X0,X2) ),
% 2.78/1.04      inference(cnf_transformation,[],[f62]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_921,plain,
% 2.78/1.04      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.78/1.04      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.78/1.04      | ~ v1_lattice3(X1)
% 2.78/1.04      | ~ l1_orders_2(X1)
% 2.78/1.04      | k13_lattice3(X1,X0,X2) = k10_lattice3(X1,X0,X2)
% 2.78/1.04      | sK2 != X1 ),
% 2.78/1.04      inference(resolution_lifted,[status(thm)],[c_19,c_26]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_922,plain,
% 2.78/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.78/1.04      | ~ v1_lattice3(sK2)
% 2.78/1.04      | ~ l1_orders_2(sK2)
% 2.78/1.04      | k13_lattice3(sK2,X0,X1) = k10_lattice3(sK2,X0,X1) ),
% 2.78/1.04      inference(unflattening,[status(thm)],[c_921]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_926,plain,
% 2.78/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.78/1.04      | k13_lattice3(sK2,X0,X1) = k10_lattice3(sK2,X0,X1) ),
% 2.78/1.04      inference(global_propositional_subsumption,
% 2.78/1.04                [status(thm)],
% 2.78/1.04                [c_922,c_25,c_23]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_927,plain,
% 2.78/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.78/1.04      | k13_lattice3(sK2,X1,X0) = k10_lattice3(sK2,X1,X0) ),
% 2.78/1.04      inference(renaming,[status(thm)],[c_926]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1118,plain,
% 2.78/1.04      ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 2.78/1.04      | k13_lattice3(sK2,X1_47,X0_47) = k10_lattice3(sK2,X1_47,X0_47) ),
% 2.78/1.04      inference(subtyping,[status(esa)],[c_927]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1883,plain,
% 2.78/1.04      ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 2.78/1.04      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.78/1.04      | k13_lattice3(sK2,sK3,sK4) = k10_lattice3(sK2,sK3,sK4) ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_1118]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1141,plain,
% 2.78/1.04      ( X0_47 != X1_47
% 2.78/1.04      | X2_47 != X3_47
% 2.78/1.04      | k12_lattice3(X0_46,X0_47,X2_47) = k12_lattice3(X0_46,X1_47,X3_47) ),
% 2.78/1.04      theory(equality) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1800,plain,
% 2.78/1.04      ( k13_lattice3(sK2,sK3,sK4) != X0_47
% 2.78/1.04      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = k12_lattice3(sK2,X1_47,X0_47)
% 2.78/1.04      | sK3 != X1_47 ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_1141]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1882,plain,
% 2.78/1.04      ( k13_lattice3(sK2,sK3,sK4) != k10_lattice3(sK2,sK3,sK4)
% 2.78/1.04      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = k12_lattice3(sK2,X0_47,k10_lattice3(sK2,sK3,sK4))
% 2.78/1.04      | sK3 != X0_47 ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_1800]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1884,plain,
% 2.78/1.04      ( k13_lattice3(sK2,sK3,sK4) != k10_lattice3(sK2,sK3,sK4)
% 2.78/1.04      | k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) = k12_lattice3(sK2,sK3,k10_lattice3(sK2,sK3,sK4))
% 2.78/1.04      | sK3 != sK3 ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_1882]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_0,plain,
% 2.78/1.04      ( r1_orders_2(X0,X1,X1)
% 2.78/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.78/1.04      | v2_struct_0(X0)
% 2.78/1.04      | ~ v3_orders_2(X0)
% 2.78/1.04      | ~ l1_orders_2(X0) ),
% 2.78/1.04      inference(cnf_transformation,[],[f43]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_27,negated_conjecture,
% 2.78/1.04      ( v3_orders_2(sK2) ),
% 2.78/1.04      inference(cnf_transformation,[],[f63]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_327,plain,
% 2.78/1.04      ( r1_orders_2(X0,X1,X1)
% 2.78/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.78/1.04      | v2_struct_0(X0)
% 2.78/1.04      | ~ l1_orders_2(X0)
% 2.78/1.04      | sK2 != X0 ),
% 2.78/1.04      inference(resolution_lifted,[status(thm)],[c_0,c_27]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_328,plain,
% 2.78/1.04      ( r1_orders_2(sK2,X0,X0)
% 2.78/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.78/1.04      | v2_struct_0(sK2)
% 2.78/1.04      | ~ l1_orders_2(sK2) ),
% 2.78/1.04      inference(unflattening,[status(thm)],[c_327]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_332,plain,
% 2.78/1.04      ( r1_orders_2(sK2,X0,X0) | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 2.78/1.04      inference(global_propositional_subsumption,
% 2.78/1.04                [status(thm)],
% 2.78/1.04                [c_328,c_24,c_23,c_82]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1132,plain,
% 2.78/1.04      ( r1_orders_2(sK2,X0_47,X0_47)
% 2.78/1.04      | ~ m1_subset_1(X0_47,u1_struct_0(sK2)) ),
% 2.78/1.04      inference(subtyping,[status(esa)],[c_332]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1152,plain,
% 2.78/1.04      ( r1_orders_2(sK2,sK3,sK3) | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_1132]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_20,negated_conjecture,
% 2.78/1.04      ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
% 2.78/1.04      inference(cnf_transformation,[],[f70]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1135,negated_conjecture,
% 2.78/1.04      ( k12_lattice3(sK2,sK3,k13_lattice3(sK2,sK3,sK4)) != sK3 ),
% 2.78/1.04      inference(subtyping,[status(esa)],[c_20]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1137,plain,( X0_47 = X0_47 ),theory(equality) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_1148,plain,
% 2.78/1.04      ( sK3 = sK3 ),
% 2.78/1.04      inference(instantiation,[status(thm)],[c_1137]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_21,negated_conjecture,
% 2.78/1.04      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 2.78/1.04      inference(cnf_transformation,[],[f69]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(c_22,negated_conjecture,
% 2.78/1.04      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.78/1.04      inference(cnf_transformation,[],[f68]) ).
% 2.78/1.04  
% 2.78/1.04  cnf(contradiction,plain,
% 2.78/1.04      ( $false ),
% 2.78/1.04      inference(minisat,
% 2.78/1.04                [status(thm)],
% 2.78/1.04                [c_4744,c_4530,c_4522,c_2645,c_2522,c_2163,c_2161,c_2083,
% 2.78/1.04                 c_1883,c_1884,c_1152,c_1135,c_1148,c_21,c_22]) ).
% 2.78/1.04  
% 2.78/1.04  
% 2.78/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 2.78/1.04  
% 2.78/1.04  ------                               Statistics
% 2.78/1.04  
% 2.78/1.04  ------ General
% 2.78/1.04  
% 2.78/1.04  abstr_ref_over_cycles:                  0
% 2.78/1.04  abstr_ref_under_cycles:                 0
% 2.78/1.04  gc_basic_clause_elim:                   0
% 2.78/1.04  forced_gc_time:                         0
% 2.78/1.04  parsing_time:                           0.011
% 2.78/1.04  unif_index_cands_time:                  0.
% 2.78/1.04  unif_index_add_time:                    0.
% 2.78/1.04  orderings_time:                         0.
% 2.78/1.04  out_proof_time:                         0.013
% 2.78/1.04  total_time:                             0.209
% 2.78/1.04  num_of_symbols:                         49
% 2.78/1.04  num_of_terms:                           4730
% 2.78/1.04  
% 2.78/1.04  ------ Preprocessing
% 2.78/1.04  
% 2.78/1.04  num_of_splits:                          0
% 2.78/1.04  num_of_split_atoms:                     0
% 2.78/1.04  num_of_reused_defs:                     0
% 2.78/1.04  num_eq_ax_congr_red:                    45
% 2.78/1.04  num_of_sem_filtered_clauses:            1
% 2.78/1.04  num_of_subtypes:                        3
% 2.78/1.04  monotx_restored_types:                  0
% 2.78/1.04  sat_num_of_epr_types:                   0
% 2.78/1.04  sat_num_of_non_cyclic_types:            0
% 2.78/1.04  sat_guarded_non_collapsed_types:        1
% 2.78/1.04  num_pure_diseq_elim:                    0
% 2.78/1.04  simp_replaced_by:                       0
% 2.78/1.04  res_preprocessed:                       107
% 2.78/1.04  prep_upred:                             0
% 2.78/1.04  prep_unflattend:                        20
% 2.78/1.04  smt_new_axioms:                         0
% 2.78/1.04  pred_elim_cands:                        2
% 2.78/1.04  pred_elim:                              6
% 2.78/1.04  pred_elim_cl:                           6
% 2.78/1.04  pred_elim_cycles:                       8
% 2.78/1.04  merged_defs:                            0
% 2.78/1.04  merged_defs_ncl:                        0
% 2.78/1.04  bin_hyper_res:                          0
% 2.78/1.04  prep_cycles:                            4
% 2.78/1.04  pred_elim_time:                         0.028
% 2.78/1.04  splitting_time:                         0.
% 2.78/1.04  sem_filter_time:                        0.
% 2.78/1.04  monotx_time:                            0.
% 2.78/1.04  subtype_inf_time:                       0.
% 2.78/1.04  
% 2.78/1.04  ------ Problem properties
% 2.78/1.04  
% 2.78/1.04  clauses:                                22
% 2.78/1.04  conjectures:                            3
% 2.78/1.04  epr:                                    0
% 2.78/1.04  horn:                                   16
% 2.78/1.04  ground:                                 3
% 2.78/1.04  unary:                                  3
% 2.78/1.04  binary:                                 1
% 2.78/1.04  lits:                                   100
% 2.78/1.04  lits_eq:                                12
% 2.78/1.04  fd_pure:                                0
% 2.78/1.04  fd_pseudo:                              0
% 2.78/1.04  fd_cond:                                0
% 2.78/1.04  fd_pseudo_cond:                         8
% 2.78/1.04  ac_symbols:                             0
% 2.78/1.04  
% 2.78/1.04  ------ Propositional Solver
% 2.78/1.04  
% 2.78/1.04  prop_solver_calls:                      28
% 2.78/1.04  prop_fast_solver_calls:                 1441
% 2.78/1.04  smt_solver_calls:                       0
% 2.78/1.04  smt_fast_solver_calls:                  0
% 2.78/1.04  prop_num_of_clauses:                    1509
% 2.78/1.04  prop_preprocess_simplified:             4609
% 2.78/1.04  prop_fo_subsumed:                       53
% 2.78/1.04  prop_solver_time:                       0.
% 2.78/1.04  smt_solver_time:                        0.
% 2.78/1.04  smt_fast_solver_time:                   0.
% 2.78/1.04  prop_fast_solver_time:                  0.
% 2.78/1.04  prop_unsat_core_time:                   0.
% 2.78/1.04  
% 2.78/1.04  ------ QBF
% 2.78/1.04  
% 2.78/1.04  qbf_q_res:                              0
% 2.78/1.04  qbf_num_tautologies:                    0
% 2.78/1.04  qbf_prep_cycles:                        0
% 2.78/1.04  
% 2.78/1.04  ------ BMC1
% 2.78/1.04  
% 2.78/1.04  bmc1_current_bound:                     -1
% 2.78/1.04  bmc1_last_solved_bound:                 -1
% 2.78/1.04  bmc1_unsat_core_size:                   -1
% 2.78/1.04  bmc1_unsat_core_parents_size:           -1
% 2.78/1.04  bmc1_merge_next_fun:                    0
% 2.78/1.04  bmc1_unsat_core_clauses_time:           0.
% 2.78/1.04  
% 2.78/1.04  ------ Instantiation
% 2.78/1.04  
% 2.78/1.04  inst_num_of_clauses:                    401
% 2.78/1.04  inst_num_in_passive:                    77
% 2.78/1.04  inst_num_in_active:                     194
% 2.78/1.04  inst_num_in_unprocessed:                129
% 2.78/1.04  inst_num_of_loops:                      213
% 2.78/1.04  inst_num_of_learning_restarts:          0
% 2.78/1.04  inst_num_moves_active_passive:          14
% 2.78/1.04  inst_lit_activity:                      0
% 2.78/1.04  inst_lit_activity_moves:                0
% 2.78/1.04  inst_num_tautologies:                   0
% 2.78/1.04  inst_num_prop_implied:                  0
% 2.78/1.04  inst_num_existing_simplified:           0
% 2.78/1.04  inst_num_eq_res_simplified:             0
% 2.78/1.04  inst_num_child_elim:                    0
% 2.78/1.04  inst_num_of_dismatching_blockings:      136
% 2.78/1.04  inst_num_of_non_proper_insts:           341
% 2.78/1.04  inst_num_of_duplicates:                 0
% 2.78/1.04  inst_inst_num_from_inst_to_res:         0
% 2.78/1.04  inst_dismatching_checking_time:         0.
% 2.78/1.04  
% 2.78/1.04  ------ Resolution
% 2.78/1.04  
% 2.78/1.04  res_num_of_clauses:                     0
% 2.78/1.04  res_num_in_passive:                     0
% 2.78/1.04  res_num_in_active:                      0
% 2.78/1.04  res_num_of_loops:                       111
% 2.78/1.04  res_forward_subset_subsumed:            41
% 2.78/1.04  res_backward_subset_subsumed:           0
% 2.78/1.04  res_forward_subsumed:                   0
% 2.78/1.04  res_backward_subsumed:                  0
% 2.78/1.04  res_forward_subsumption_resolution:     0
% 2.78/1.04  res_backward_subsumption_resolution:    3
% 2.78/1.04  res_clause_to_clause_subsumption:       574
% 2.78/1.04  res_orphan_elimination:                 0
% 2.78/1.04  res_tautology_del:                      54
% 2.78/1.04  res_num_eq_res_simplified:              0
% 2.78/1.04  res_num_sel_changes:                    0
% 2.78/1.04  res_moves_from_active_to_pass:          0
% 2.78/1.04  
% 2.78/1.04  ------ Superposition
% 2.78/1.04  
% 2.78/1.04  sup_time_total:                         0.
% 2.78/1.04  sup_time_generating:                    0.
% 2.78/1.04  sup_time_sim_full:                      0.
% 2.78/1.04  sup_time_sim_immed:                     0.
% 2.78/1.04  
% 2.78/1.04  sup_num_of_clauses:                     93
% 2.78/1.04  sup_num_in_active:                      40
% 2.78/1.04  sup_num_in_passive:                     53
% 2.78/1.04  sup_num_of_loops:                       42
% 2.78/1.04  sup_fw_superposition:                   44
% 2.78/1.04  sup_bw_superposition:                   35
% 2.78/1.04  sup_immediate_simplified:               10
% 2.78/1.04  sup_given_eliminated:                   0
% 2.78/1.04  comparisons_done:                       0
% 2.78/1.04  comparisons_avoided:                    0
% 2.78/1.04  
% 2.78/1.04  ------ Simplifications
% 2.78/1.04  
% 2.78/1.04  
% 2.78/1.04  sim_fw_subset_subsumed:                 0
% 2.78/1.04  sim_bw_subset_subsumed:                 0
% 2.78/1.04  sim_fw_subsumed:                        0
% 2.78/1.04  sim_bw_subsumed:                        0
% 2.78/1.04  sim_fw_subsumption_res:                 0
% 2.78/1.04  sim_bw_subsumption_res:                 0
% 2.78/1.04  sim_tautology_del:                      0
% 2.78/1.04  sim_eq_tautology_del:                   2
% 2.78/1.04  sim_eq_res_simp:                        0
% 2.78/1.04  sim_fw_demodulated:                     0
% 2.78/1.04  sim_bw_demodulated:                     2
% 2.78/1.04  sim_light_normalised:                   10
% 2.78/1.04  sim_joinable_taut:                      0
% 2.78/1.04  sim_joinable_simp:                      0
% 2.78/1.04  sim_ac_normalised:                      0
% 2.78/1.04  sim_smt_subsumption:                    0
% 2.78/1.04  
%------------------------------------------------------------------------------
