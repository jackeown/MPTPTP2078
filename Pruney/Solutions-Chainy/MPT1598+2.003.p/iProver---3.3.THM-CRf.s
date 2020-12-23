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
% DateTime   : Thu Dec  3 12:20:05 EST 2020

% Result     : Theorem 3.68s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :  154 (1180 expanded)
%              Number of clauses        :   92 ( 413 expanded)
%              Number of leaves         :   16 ( 299 expanded)
%              Depth                    :   25
%              Number of atoms          :  730 (4595 expanded)
%              Number of equality atoms :  181 ( 712 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   21 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f18,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f64,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f62,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f13,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_lattice3(k2_yellow_1(X0))
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
               => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( v1_lattice3(k2_yellow_1(X0))
         => ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
                 => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v1_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v1_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))
          & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
     => ( ~ r1_tarski(k2_xboole_0(X1,sK3),k10_lattice3(k2_yellow_1(X0),X1,sK3))
        & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
     => ( ? [X2] :
            ( ~ r1_tarski(k2_xboole_0(sK2,X2),k10_lattice3(k2_yellow_1(X0),sK2,X2))
            & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
        & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))
                & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
            & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
        & v1_lattice3(k2_yellow_1(X0))
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(sK1),X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK1))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1))) )
      & v1_lattice3(k2_yellow_1(sK1))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ~ r1_tarski(k2_xboole_0(sK2,sK3),k10_lattice3(k2_yellow_1(sK1),sK2,sK3))
    & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
    & v1_lattice3(k2_yellow_1(sK1))
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f36,f46,f45,f44])).

fof(f72,plain,(
    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f73,plain,(
    m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f71,plain,(
    v1_lattice3(k2_yellow_1(sK1)) ),
    inference(cnf_transformation,[],[f47])).

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

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

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
    inference(nnf_transformation,[],[f28])).

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
    inference(cnf_transformation,[],[f42])).

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
    inference(equality_resolution,[],[f53])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f63,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
                  | ~ r1_tarski(X1,X2) )
                & ( r1_tarski(X1,X2)
                  | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f70,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f74,plain,(
    ~ r1_tarski(k2_xboole_0(sK2,sK3),k10_lattice3(k2_yellow_1(sK1),sK2,sK3)) ),
    inference(cnf_transformation,[],[f47])).

fof(f7,axiom,(
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

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k13_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_15,plain,
    ( v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_907,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k13_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k2_yellow_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_15])).

cnf(c_908,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | m1_subset_1(k13_lattice3(k2_yellow_1(X1),X0,X2),u1_struct_0(k2_yellow_1(X1)))
    | ~ v1_lattice3(k2_yellow_1(X1))
    | ~ l1_orders_2(k2_yellow_1(X1)) ),
    inference(unflattening,[status(thm)],[c_907])).

cnf(c_14,plain,
    ( l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_922,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | m1_subset_1(k13_lattice3(k2_yellow_1(X1),X2,X0),u1_struct_0(k2_yellow_1(X1)))
    | ~ v1_lattice3(k2_yellow_1(X1)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_908,c_14])).

cnf(c_2718,plain,
    ( m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) != iProver_top
    | m1_subset_1(k13_lattice3(k2_yellow_1(X1),X2,X0),u1_struct_0(k2_yellow_1(X1))) = iProver_top
    | v1_lattice3(k2_yellow_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_922])).

cnf(c_19,plain,
    ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2753,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,X1) != iProver_top
    | m1_subset_1(k13_lattice3(k2_yellow_1(X1),X2,X0),X1) = iProver_top
    | v1_lattice3(k2_yellow_1(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2718,c_19])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2729,plain,
    ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2739,plain,
    ( m1_subset_1(sK2,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2729,c_19])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2730,plain,
    ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2742,plain,
    ( m1_subset_1(sK3,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2730,c_19])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_884,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0)
    | k2_yellow_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_15])).

cnf(c_885,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | ~ v1_lattice3(k2_yellow_1(X1))
    | ~ l1_orders_2(k2_yellow_1(X1))
    | k10_lattice3(k2_yellow_1(X1),X0,X2) = k13_lattice3(k2_yellow_1(X1),X0,X2) ),
    inference(unflattening,[status(thm)],[c_884])).

cnf(c_899,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | ~ v1_lattice3(k2_yellow_1(X1))
    | k10_lattice3(k2_yellow_1(X1),X2,X0) = k13_lattice3(k2_yellow_1(X1),X2,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_885,c_14])).

cnf(c_2719,plain,
    ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k13_lattice3(k2_yellow_1(X0),X1,X2)
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | v1_lattice3(k2_yellow_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_899])).

cnf(c_2762,plain,
    ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k13_lattice3(k2_yellow_1(X0),X1,X2)
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | v1_lattice3(k2_yellow_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2719,c_19])).

cnf(c_3778,plain,
    ( k10_lattice3(k2_yellow_1(sK1),X0,sK3) = k13_lattice3(k2_yellow_1(sK1),X0,sK3)
    | m1_subset_1(X0,sK1) != iProver_top
    | v1_lattice3(k2_yellow_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2742,c_2762])).

cnf(c_25,negated_conjecture,
    ( v1_lattice3(k2_yellow_1(sK1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_28,plain,
    ( v1_lattice3(k2_yellow_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4431,plain,
    ( m1_subset_1(X0,sK1) != iProver_top
    | k10_lattice3(k2_yellow_1(sK1),X0,sK3) = k13_lattice3(k2_yellow_1(sK1),X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3778,c_28])).

cnf(c_4432,plain,
    ( k10_lattice3(k2_yellow_1(sK1),X0,sK3) = k13_lattice3(k2_yellow_1(sK1),X0,sK3)
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4431])).

cnf(c_4439,plain,
    ( k10_lattice3(k2_yellow_1(sK1),sK2,sK3) = k13_lattice3(k2_yellow_1(sK1),sK2,sK3) ),
    inference(superposition,[status(thm)],[c_2739,c_4432])).

cnf(c_11,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_3,plain,
    ( ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_154,plain,
    ( ~ v1_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_3])).

cnf(c_155,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_154])).

cnf(c_838,plain,
    ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_155,c_15])).

cnf(c_839,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,k10_lattice3(k2_yellow_1(X0),X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(k10_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
    | ~ v1_lattice3(k2_yellow_1(X0))
    | ~ l1_orders_2(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_838])).

cnf(c_841,plain,
    ( ~ v1_lattice3(k2_yellow_1(X0))
    | ~ m1_subset_1(k10_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | r1_orders_2(k2_yellow_1(X0),X1,k10_lattice3(k2_yellow_1(X0),X1,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_839,c_14])).

cnf(c_842,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,k10_lattice3(k2_yellow_1(X0),X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(k10_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
    | ~ v1_lattice3(k2_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_841])).

cnf(c_2721,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,k10_lattice3(k2_yellow_1(X0),X1,X2)) = iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(k10_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | v1_lattice3(k2_yellow_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_842])).

cnf(c_2780,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,k10_lattice3(k2_yellow_1(X0),X1,X2)) = iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(k10_lattice3(k2_yellow_1(X0),X1,X2),X0) != iProver_top
    | v1_lattice3(k2_yellow_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2721,c_19])).

cnf(c_1,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_16,plain,
    ( v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_404,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_16])).

cnf(c_405,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | v2_struct_0(k2_yellow_1(X0))
    | ~ l1_orders_2(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_409,plain,
    ( v2_struct_0(k2_yellow_1(X0))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r1_orders_2(k2_yellow_1(X0),X1,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_405,c_14])).

cnf(c_410,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | v2_struct_0(k2_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_409])).

cnf(c_21,plain,
    ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | r1_tarski(X1,X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_26,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_322,plain,
    ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | r1_tarski(X1,X2)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_26])).

cnf(c_323,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK1),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | r1_tarski(X0,X1) ),
    inference(unflattening,[status(thm)],[c_322])).

cnf(c_1649,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X4,u1_struct_0(k2_yellow_1(sK1)))
    | r1_tarski(X4,X3)
    | v2_struct_0(k2_yellow_1(X0))
    | X4 != X1
    | X3 != X2
    | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_410,c_323])).

cnf(c_1650,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
    | r1_tarski(X1,X2)
    | v2_struct_0(k2_yellow_1(X0))
    | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
    inference(unflattening,[status(thm)],[c_1649])).

cnf(c_559,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X4,u1_struct_0(k2_yellow_1(sK1)))
    | r1_tarski(X4,X3)
    | v2_struct_0(k2_yellow_1(X0))
    | X4 != X1
    | X3 != X2
    | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_410,c_323])).

cnf(c_560,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
    | r1_tarski(X1,X2)
    | v2_struct_0(k2_yellow_1(X0))
    | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
    inference(unflattening,[status(thm)],[c_559])).

cnf(c_1002,plain,
    ( ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0)
    | k2_yellow_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_14])).

cnf(c_1003,plain,
    ( ~ v1_lattice3(k2_yellow_1(X0))
    | ~ v2_struct_0(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_1002])).

cnf(c_1107,plain,
    ( ~ v2_struct_0(k2_yellow_1(X0))
    | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_25,c_1003])).

cnf(c_1652,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1650,c_560,c_1107])).

cnf(c_1653,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
    | r1_tarski(X1,X2)
    | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
    inference(renaming,[status(thm)],[c_1652])).

cnf(c_2717,plain,
    ( k2_yellow_1(X0) != k2_yellow_1(sK1)
    | r1_orders_2(k2_yellow_1(X0),X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
    | r1_tarski(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1653])).

cnf(c_2818,plain,
    ( k2_yellow_1(X0) != k2_yellow_1(sK1)
    | r1_orders_2(k2_yellow_1(X0),X1,X2) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
    | r1_tarski(X1,X2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2717,c_19])).

cnf(c_2819,plain,
    ( k2_yellow_1(X0) != k2_yellow_1(sK1)
    | r1_orders_2(k2_yellow_1(X0),X1,X2) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X1,sK1) != iProver_top
    | m1_subset_1(X2,sK1) != iProver_top
    | r1_tarski(X1,X2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2818,c_19])).

cnf(c_3140,plain,
    ( r1_orders_2(k2_yellow_1(sK1),X0,X1) != iProver_top
    | m1_subset_1(X1,sK1) != iProver_top
    | m1_subset_1(X0,sK1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2819])).

cnf(c_4735,plain,
    ( m1_subset_1(X0,sK1) != iProver_top
    | m1_subset_1(X1,sK1) != iProver_top
    | m1_subset_1(k10_lattice3(k2_yellow_1(sK1),X0,X1),sK1) != iProver_top
    | r1_tarski(X0,k10_lattice3(k2_yellow_1(sK1),X0,X1)) = iProver_top
    | v1_lattice3(k2_yellow_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2780,c_3140])).

cnf(c_8839,plain,
    ( r1_tarski(X0,k10_lattice3(k2_yellow_1(sK1),X0,X1)) = iProver_top
    | m1_subset_1(k10_lattice3(k2_yellow_1(sK1),X0,X1),sK1) != iProver_top
    | m1_subset_1(X1,sK1) != iProver_top
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4735,c_28])).

cnf(c_8840,plain,
    ( m1_subset_1(X0,sK1) != iProver_top
    | m1_subset_1(X1,sK1) != iProver_top
    | m1_subset_1(k10_lattice3(k2_yellow_1(sK1),X1,X0),sK1) != iProver_top
    | r1_tarski(X1,k10_lattice3(k2_yellow_1(sK1),X1,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_8839])).

cnf(c_8849,plain,
    ( m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),sK1) != iProver_top
    | m1_subset_1(sK3,sK1) != iProver_top
    | m1_subset_1(sK2,sK1) != iProver_top
    | r1_tarski(sK2,k10_lattice3(k2_yellow_1(sK1),sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4439,c_8840])).

cnf(c_8964,plain,
    ( m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),sK1) != iProver_top
    | m1_subset_1(sK3,sK1) != iProver_top
    | m1_subset_1(sK2,sK1) != iProver_top
    | r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8849,c_4439])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X2,X0),X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2732,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_22,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(sK2,sK3),k10_lattice3(k2_yellow_1(sK1),sK2,sK3)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2731,plain,
    ( r1_tarski(k2_xboole_0(sK2,sK3),k10_lattice3(k2_yellow_1(sK1),sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3705,plain,
    ( r1_tarski(sK3,k10_lattice3(k2_yellow_1(sK1),sK2,sK3)) != iProver_top
    | r1_tarski(sK2,k10_lattice3(k2_yellow_1(sK1),sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2732,c_2731])).

cnf(c_4458,plain,
    ( r1_tarski(sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3)) != iProver_top
    | r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4439,c_3705])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k10_lattice3(X1,X0,X2) = k10_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_861,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k10_lattice3(X1,X0,X2) = k10_lattice3(X1,X2,X0)
    | k2_yellow_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_15])).

cnf(c_862,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | ~ v1_lattice3(k2_yellow_1(X1))
    | ~ l1_orders_2(k2_yellow_1(X1))
    | k10_lattice3(k2_yellow_1(X1),X2,X0) = k10_lattice3(k2_yellow_1(X1),X0,X2) ),
    inference(unflattening,[status(thm)],[c_861])).

cnf(c_876,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | ~ v1_lattice3(k2_yellow_1(X1))
    | k10_lattice3(k2_yellow_1(X1),X0,X2) = k10_lattice3(k2_yellow_1(X1),X2,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_862,c_14])).

cnf(c_2720,plain,
    ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k10_lattice3(k2_yellow_1(X0),X2,X1)
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | v1_lattice3(k2_yellow_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_876])).

cnf(c_2771,plain,
    ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k10_lattice3(k2_yellow_1(X0),X2,X1)
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | v1_lattice3(k2_yellow_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2720,c_19])).

cnf(c_4481,plain,
    ( k10_lattice3(k2_yellow_1(sK1),X0,sK2) = k10_lattice3(k2_yellow_1(sK1),sK2,X0)
    | m1_subset_1(X0,sK1) != iProver_top
    | v1_lattice3(k2_yellow_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2739,c_2771])).

cnf(c_5165,plain,
    ( m1_subset_1(X0,sK1) != iProver_top
    | k10_lattice3(k2_yellow_1(sK1),X0,sK2) = k10_lattice3(k2_yellow_1(sK1),sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4481,c_28])).

cnf(c_5166,plain,
    ( k10_lattice3(k2_yellow_1(sK1),X0,sK2) = k10_lattice3(k2_yellow_1(sK1),sK2,X0)
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5165])).

cnf(c_5174,plain,
    ( k10_lattice3(k2_yellow_1(sK1),sK3,sK2) = k10_lattice3(k2_yellow_1(sK1),sK2,sK3) ),
    inference(superposition,[status(thm)],[c_2742,c_5166])).

cnf(c_3777,plain,
    ( k10_lattice3(k2_yellow_1(sK1),X0,sK2) = k13_lattice3(k2_yellow_1(sK1),X0,sK2)
    | m1_subset_1(X0,sK1) != iProver_top
    | v1_lattice3(k2_yellow_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2739,c_2762])).

cnf(c_3815,plain,
    ( m1_subset_1(X0,sK1) != iProver_top
    | k10_lattice3(k2_yellow_1(sK1),X0,sK2) = k13_lattice3(k2_yellow_1(sK1),X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3777,c_28])).

cnf(c_3816,plain,
    ( k10_lattice3(k2_yellow_1(sK1),X0,sK2) = k13_lattice3(k2_yellow_1(sK1),X0,sK2)
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3815])).

cnf(c_3824,plain,
    ( k10_lattice3(k2_yellow_1(sK1),sK3,sK2) = k13_lattice3(k2_yellow_1(sK1),sK3,sK2) ),
    inference(superposition,[status(thm)],[c_2742,c_3816])).

cnf(c_5202,plain,
    ( k13_lattice3(k2_yellow_1(sK1),sK3,sK2) = k13_lattice3(k2_yellow_1(sK1),sK2,sK3) ),
    inference(light_normalisation,[status(thm)],[c_5174,c_3824,c_4439])).

cnf(c_5464,plain,
    ( k10_lattice3(k2_yellow_1(sK1),sK3,sK2) = k13_lattice3(k2_yellow_1(sK1),sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_5202,c_3824])).

cnf(c_8851,plain,
    ( m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),sK1) != iProver_top
    | m1_subset_1(sK3,sK1) != iProver_top
    | m1_subset_1(sK2,sK1) != iProver_top
    | r1_tarski(sK3,k10_lattice3(k2_yellow_1(sK1),sK3,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5464,c_8840])).

cnf(c_8951,plain,
    ( m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),sK1) != iProver_top
    | m1_subset_1(sK3,sK1) != iProver_top
    | m1_subset_1(sK2,sK1) != iProver_top
    | r1_tarski(sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8851,c_5464])).

cnf(c_9717,plain,
    ( m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8964,c_2739,c_2742,c_4458,c_8951])).

cnf(c_9722,plain,
    ( m1_subset_1(sK3,sK1) != iProver_top
    | m1_subset_1(sK2,sK1) != iProver_top
    | v1_lattice3(k2_yellow_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2753,c_9717])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9722,c_2742,c_2739,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:26:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.68/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.68/0.98  
% 3.68/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.68/0.98  
% 3.68/0.98  ------  iProver source info
% 3.68/0.98  
% 3.68/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.68/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.68/0.98  git: non_committed_changes: false
% 3.68/0.98  git: last_make_outside_of_git: false
% 3.68/0.98  
% 3.68/0.98  ------ 
% 3.68/0.98  
% 3.68/0.98  ------ Input Options
% 3.68/0.98  
% 3.68/0.98  --out_options                           all
% 3.68/0.98  --tptp_safe_out                         true
% 3.68/0.98  --problem_path                          ""
% 3.68/0.98  --include_path                          ""
% 3.68/0.98  --clausifier                            res/vclausify_rel
% 3.68/0.98  --clausifier_options                    --mode clausify
% 3.68/0.98  --stdin                                 false
% 3.68/0.98  --stats_out                             all
% 3.68/0.98  
% 3.68/0.98  ------ General Options
% 3.68/0.98  
% 3.68/0.98  --fof                                   false
% 3.68/0.98  --time_out_real                         305.
% 3.68/0.98  --time_out_virtual                      -1.
% 3.68/0.98  --symbol_type_check                     false
% 3.68/0.98  --clausify_out                          false
% 3.68/0.98  --sig_cnt_out                           false
% 3.68/0.98  --trig_cnt_out                          false
% 3.68/0.98  --trig_cnt_out_tolerance                1.
% 3.68/0.98  --trig_cnt_out_sk_spl                   false
% 3.68/0.98  --abstr_cl_out                          false
% 3.68/0.98  
% 3.68/0.98  ------ Global Options
% 3.68/0.98  
% 3.68/0.98  --schedule                              default
% 3.68/0.98  --add_important_lit                     false
% 3.68/0.98  --prop_solver_per_cl                    1000
% 3.68/0.98  --min_unsat_core                        false
% 3.68/0.98  --soft_assumptions                      false
% 3.68/0.98  --soft_lemma_size                       3
% 3.68/0.98  --prop_impl_unit_size                   0
% 3.68/0.98  --prop_impl_unit                        []
% 3.68/0.98  --share_sel_clauses                     true
% 3.68/0.98  --reset_solvers                         false
% 3.68/0.98  --bc_imp_inh                            [conj_cone]
% 3.68/0.98  --conj_cone_tolerance                   3.
% 3.68/0.98  --extra_neg_conj                        none
% 3.68/0.98  --large_theory_mode                     true
% 3.68/0.98  --prolific_symb_bound                   200
% 3.68/0.98  --lt_threshold                          2000
% 3.68/0.98  --clause_weak_htbl                      true
% 3.68/0.98  --gc_record_bc_elim                     false
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing Options
% 3.68/0.98  
% 3.68/0.98  --preprocessing_flag                    true
% 3.68/0.98  --time_out_prep_mult                    0.1
% 3.68/0.98  --splitting_mode                        input
% 3.68/0.98  --splitting_grd                         true
% 3.68/0.98  --splitting_cvd                         false
% 3.68/0.98  --splitting_cvd_svl                     false
% 3.68/0.98  --splitting_nvd                         32
% 3.68/0.98  --sub_typing                            true
% 3.68/0.98  --prep_gs_sim                           true
% 3.68/0.98  --prep_unflatten                        true
% 3.68/0.98  --prep_res_sim                          true
% 3.68/0.98  --prep_upred                            true
% 3.68/0.98  --prep_sem_filter                       exhaustive
% 3.68/0.98  --prep_sem_filter_out                   false
% 3.68/0.98  --pred_elim                             true
% 3.68/0.98  --res_sim_input                         true
% 3.68/0.98  --eq_ax_congr_red                       true
% 3.68/0.98  --pure_diseq_elim                       true
% 3.68/0.98  --brand_transform                       false
% 3.68/0.98  --non_eq_to_eq                          false
% 3.68/0.98  --prep_def_merge                        true
% 3.68/0.98  --prep_def_merge_prop_impl              false
% 3.68/0.98  --prep_def_merge_mbd                    true
% 3.68/0.98  --prep_def_merge_tr_red                 false
% 3.68/0.98  --prep_def_merge_tr_cl                  false
% 3.68/0.98  --smt_preprocessing                     true
% 3.68/0.98  --smt_ac_axioms                         fast
% 3.68/0.98  --preprocessed_out                      false
% 3.68/0.98  --preprocessed_stats                    false
% 3.68/0.98  
% 3.68/0.98  ------ Abstraction refinement Options
% 3.68/0.98  
% 3.68/0.98  --abstr_ref                             []
% 3.68/0.98  --abstr_ref_prep                        false
% 3.68/0.98  --abstr_ref_until_sat                   false
% 3.68/0.98  --abstr_ref_sig_restrict                funpre
% 3.68/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.68/0.98  --abstr_ref_under                       []
% 3.68/0.98  
% 3.68/0.98  ------ SAT Options
% 3.68/0.98  
% 3.68/0.98  --sat_mode                              false
% 3.68/0.98  --sat_fm_restart_options                ""
% 3.68/0.98  --sat_gr_def                            false
% 3.68/0.98  --sat_epr_types                         true
% 3.68/0.98  --sat_non_cyclic_types                  false
% 3.68/0.98  --sat_finite_models                     false
% 3.68/0.98  --sat_fm_lemmas                         false
% 3.68/0.98  --sat_fm_prep                           false
% 3.68/0.98  --sat_fm_uc_incr                        true
% 3.68/0.98  --sat_out_model                         small
% 3.68/0.98  --sat_out_clauses                       false
% 3.68/0.98  
% 3.68/0.98  ------ QBF Options
% 3.68/0.98  
% 3.68/0.98  --qbf_mode                              false
% 3.68/0.98  --qbf_elim_univ                         false
% 3.68/0.98  --qbf_dom_inst                          none
% 3.68/0.98  --qbf_dom_pre_inst                      false
% 3.68/0.98  --qbf_sk_in                             false
% 3.68/0.98  --qbf_pred_elim                         true
% 3.68/0.98  --qbf_split                             512
% 3.68/0.98  
% 3.68/0.98  ------ BMC1 Options
% 3.68/0.98  
% 3.68/0.98  --bmc1_incremental                      false
% 3.68/0.98  --bmc1_axioms                           reachable_all
% 3.68/0.98  --bmc1_min_bound                        0
% 3.68/0.98  --bmc1_max_bound                        -1
% 3.68/0.98  --bmc1_max_bound_default                -1
% 3.68/0.98  --bmc1_symbol_reachability              true
% 3.68/0.98  --bmc1_property_lemmas                  false
% 3.68/0.98  --bmc1_k_induction                      false
% 3.68/0.98  --bmc1_non_equiv_states                 false
% 3.68/0.98  --bmc1_deadlock                         false
% 3.68/0.98  --bmc1_ucm                              false
% 3.68/0.98  --bmc1_add_unsat_core                   none
% 3.68/0.98  --bmc1_unsat_core_children              false
% 3.68/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.68/0.98  --bmc1_out_stat                         full
% 3.68/0.98  --bmc1_ground_init                      false
% 3.68/0.98  --bmc1_pre_inst_next_state              false
% 3.68/0.98  --bmc1_pre_inst_state                   false
% 3.68/0.98  --bmc1_pre_inst_reach_state             false
% 3.68/0.98  --bmc1_out_unsat_core                   false
% 3.68/0.98  --bmc1_aig_witness_out                  false
% 3.68/0.98  --bmc1_verbose                          false
% 3.68/0.98  --bmc1_dump_clauses_tptp                false
% 3.68/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.68/0.98  --bmc1_dump_file                        -
% 3.68/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.68/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.68/0.98  --bmc1_ucm_extend_mode                  1
% 3.68/0.98  --bmc1_ucm_init_mode                    2
% 3.68/0.98  --bmc1_ucm_cone_mode                    none
% 3.68/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.68/0.98  --bmc1_ucm_relax_model                  4
% 3.68/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.68/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.68/0.98  --bmc1_ucm_layered_model                none
% 3.68/0.98  --bmc1_ucm_max_lemma_size               10
% 3.68/0.98  
% 3.68/0.98  ------ AIG Options
% 3.68/0.98  
% 3.68/0.98  --aig_mode                              false
% 3.68/0.98  
% 3.68/0.98  ------ Instantiation Options
% 3.68/0.98  
% 3.68/0.98  --instantiation_flag                    true
% 3.68/0.98  --inst_sos_flag                         false
% 3.68/0.98  --inst_sos_phase                        true
% 3.68/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.68/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.68/0.98  --inst_lit_sel_side                     num_symb
% 3.68/0.98  --inst_solver_per_active                1400
% 3.68/0.98  --inst_solver_calls_frac                1.
% 3.68/0.98  --inst_passive_queue_type               priority_queues
% 3.68/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.68/0.98  --inst_passive_queues_freq              [25;2]
% 3.68/0.98  --inst_dismatching                      true
% 3.68/0.98  --inst_eager_unprocessed_to_passive     true
% 3.68/0.98  --inst_prop_sim_given                   true
% 3.68/0.98  --inst_prop_sim_new                     false
% 3.68/0.98  --inst_subs_new                         false
% 3.68/0.98  --inst_eq_res_simp                      false
% 3.68/0.98  --inst_subs_given                       false
% 3.68/0.98  --inst_orphan_elimination               true
% 3.68/0.98  --inst_learning_loop_flag               true
% 3.68/0.98  --inst_learning_start                   3000
% 3.68/0.98  --inst_learning_factor                  2
% 3.68/0.98  --inst_start_prop_sim_after_learn       3
% 3.68/0.98  --inst_sel_renew                        solver
% 3.68/0.98  --inst_lit_activity_flag                true
% 3.68/0.98  --inst_restr_to_given                   false
% 3.68/0.98  --inst_activity_threshold               500
% 3.68/0.98  --inst_out_proof                        true
% 3.68/0.98  
% 3.68/0.98  ------ Resolution Options
% 3.68/0.98  
% 3.68/0.98  --resolution_flag                       true
% 3.68/0.98  --res_lit_sel                           adaptive
% 3.68/0.98  --res_lit_sel_side                      none
% 3.68/0.98  --res_ordering                          kbo
% 3.68/0.98  --res_to_prop_solver                    active
% 3.68/0.98  --res_prop_simpl_new                    false
% 3.68/0.98  --res_prop_simpl_given                  true
% 3.68/0.98  --res_passive_queue_type                priority_queues
% 3.68/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.68/0.98  --res_passive_queues_freq               [15;5]
% 3.68/0.98  --res_forward_subs                      full
% 3.68/0.98  --res_backward_subs                     full
% 3.68/0.98  --res_forward_subs_resolution           true
% 3.68/0.98  --res_backward_subs_resolution          true
% 3.68/0.98  --res_orphan_elimination                true
% 3.68/0.98  --res_time_limit                        2.
% 3.68/0.98  --res_out_proof                         true
% 3.68/0.98  
% 3.68/0.98  ------ Superposition Options
% 3.68/0.98  
% 3.68/0.98  --superposition_flag                    true
% 3.68/0.98  --sup_passive_queue_type                priority_queues
% 3.68/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.68/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.68/0.98  --demod_completeness_check              fast
% 3.68/0.98  --demod_use_ground                      true
% 3.68/0.98  --sup_to_prop_solver                    passive
% 3.68/0.98  --sup_prop_simpl_new                    true
% 3.68/0.98  --sup_prop_simpl_given                  true
% 3.68/0.98  --sup_fun_splitting                     false
% 3.68/0.98  --sup_smt_interval                      50000
% 3.68/0.98  
% 3.68/0.98  ------ Superposition Simplification Setup
% 3.68/0.98  
% 3.68/0.98  --sup_indices_passive                   []
% 3.68/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.68/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.68/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.68/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.68/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.68/0.98  --sup_full_bw                           [BwDemod]
% 3.68/0.98  --sup_immed_triv                        [TrivRules]
% 3.68/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.68/0.98  --sup_immed_bw_main                     []
% 3.68/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.68/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.68/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.68/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.68/0.98  
% 3.68/0.98  ------ Combination Options
% 3.68/0.98  
% 3.68/0.98  --comb_res_mult                         3
% 3.68/0.98  --comb_sup_mult                         2
% 3.68/0.98  --comb_inst_mult                        10
% 3.68/0.98  
% 3.68/0.98  ------ Debug Options
% 3.68/0.98  
% 3.68/0.98  --dbg_backtrace                         false
% 3.68/0.98  --dbg_dump_prop_clauses                 false
% 3.68/0.98  --dbg_dump_prop_clauses_file            -
% 3.68/0.98  --dbg_out_stat                          false
% 3.68/0.98  ------ Parsing...
% 3.68/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.68/0.98  ------ Proving...
% 3.68/0.98  ------ Problem Properties 
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  clauses                                 19
% 3.68/0.98  conjectures                             4
% 3.68/0.98  EPR                                     0
% 3.68/0.98  Horn                                    16
% 3.68/0.98  unary                                   6
% 3.68/0.98  binary                                  0
% 3.68/0.98  lits                                    85
% 3.68/0.98  lits eq                                 10
% 3.68/0.98  fd_pure                                 0
% 3.68/0.98  fd_pseudo                               0
% 3.68/0.98  fd_cond                                 0
% 3.68/0.98  fd_pseudo_cond                          4
% 3.68/0.98  AC symbols                              0
% 3.68/0.98  
% 3.68/0.98  ------ Schedule dynamic 5 is on 
% 3.68/0.98  
% 3.68/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  ------ 
% 3.68/0.98  Current options:
% 3.68/0.98  ------ 
% 3.68/0.98  
% 3.68/0.98  ------ Input Options
% 3.68/0.98  
% 3.68/0.98  --out_options                           all
% 3.68/0.98  --tptp_safe_out                         true
% 3.68/0.98  --problem_path                          ""
% 3.68/0.98  --include_path                          ""
% 3.68/0.98  --clausifier                            res/vclausify_rel
% 3.68/0.98  --clausifier_options                    --mode clausify
% 3.68/0.98  --stdin                                 false
% 3.68/0.98  --stats_out                             all
% 3.68/0.98  
% 3.68/0.98  ------ General Options
% 3.68/0.98  
% 3.68/0.98  --fof                                   false
% 3.68/0.98  --time_out_real                         305.
% 3.68/0.98  --time_out_virtual                      -1.
% 3.68/0.98  --symbol_type_check                     false
% 3.68/0.98  --clausify_out                          false
% 3.68/0.98  --sig_cnt_out                           false
% 3.68/0.98  --trig_cnt_out                          false
% 3.68/0.98  --trig_cnt_out_tolerance                1.
% 3.68/0.98  --trig_cnt_out_sk_spl                   false
% 3.68/0.98  --abstr_cl_out                          false
% 3.68/0.98  
% 3.68/0.98  ------ Global Options
% 3.68/0.98  
% 3.68/0.98  --schedule                              default
% 3.68/0.98  --add_important_lit                     false
% 3.68/0.98  --prop_solver_per_cl                    1000
% 3.68/0.98  --min_unsat_core                        false
% 3.68/0.98  --soft_assumptions                      false
% 3.68/0.98  --soft_lemma_size                       3
% 3.68/0.98  --prop_impl_unit_size                   0
% 3.68/0.98  --prop_impl_unit                        []
% 3.68/0.98  --share_sel_clauses                     true
% 3.68/0.98  --reset_solvers                         false
% 3.68/0.98  --bc_imp_inh                            [conj_cone]
% 3.68/0.98  --conj_cone_tolerance                   3.
% 3.68/0.98  --extra_neg_conj                        none
% 3.68/0.98  --large_theory_mode                     true
% 3.68/0.98  --prolific_symb_bound                   200
% 3.68/0.98  --lt_threshold                          2000
% 3.68/0.98  --clause_weak_htbl                      true
% 3.68/0.98  --gc_record_bc_elim                     false
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing Options
% 3.68/0.98  
% 3.68/0.98  --preprocessing_flag                    true
% 3.68/0.98  --time_out_prep_mult                    0.1
% 3.68/0.98  --splitting_mode                        input
% 3.68/0.98  --splitting_grd                         true
% 3.68/0.98  --splitting_cvd                         false
% 3.68/0.98  --splitting_cvd_svl                     false
% 3.68/0.98  --splitting_nvd                         32
% 3.68/0.98  --sub_typing                            true
% 3.68/0.98  --prep_gs_sim                           true
% 3.68/0.98  --prep_unflatten                        true
% 3.68/0.98  --prep_res_sim                          true
% 3.68/0.98  --prep_upred                            true
% 3.68/0.98  --prep_sem_filter                       exhaustive
% 3.68/0.98  --prep_sem_filter_out                   false
% 3.68/0.98  --pred_elim                             true
% 3.68/0.98  --res_sim_input                         true
% 3.68/0.98  --eq_ax_congr_red                       true
% 3.68/0.98  --pure_diseq_elim                       true
% 3.68/0.98  --brand_transform                       false
% 3.68/0.98  --non_eq_to_eq                          false
% 3.68/0.98  --prep_def_merge                        true
% 3.68/0.98  --prep_def_merge_prop_impl              false
% 3.68/0.98  --prep_def_merge_mbd                    true
% 3.68/0.98  --prep_def_merge_tr_red                 false
% 3.68/0.98  --prep_def_merge_tr_cl                  false
% 3.68/0.98  --smt_preprocessing                     true
% 3.68/0.98  --smt_ac_axioms                         fast
% 3.68/0.98  --preprocessed_out                      false
% 3.68/0.98  --preprocessed_stats                    false
% 3.68/0.98  
% 3.68/0.98  ------ Abstraction refinement Options
% 3.68/0.98  
% 3.68/0.98  --abstr_ref                             []
% 3.68/0.98  --abstr_ref_prep                        false
% 3.68/0.98  --abstr_ref_until_sat                   false
% 3.68/0.98  --abstr_ref_sig_restrict                funpre
% 3.68/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.68/0.98  --abstr_ref_under                       []
% 3.68/0.98  
% 3.68/0.98  ------ SAT Options
% 3.68/0.98  
% 3.68/0.98  --sat_mode                              false
% 3.68/0.98  --sat_fm_restart_options                ""
% 3.68/0.98  --sat_gr_def                            false
% 3.68/0.98  --sat_epr_types                         true
% 3.68/0.98  --sat_non_cyclic_types                  false
% 3.68/0.98  --sat_finite_models                     false
% 3.68/0.98  --sat_fm_lemmas                         false
% 3.68/0.98  --sat_fm_prep                           false
% 3.68/0.98  --sat_fm_uc_incr                        true
% 3.68/0.98  --sat_out_model                         small
% 3.68/0.98  --sat_out_clauses                       false
% 3.68/0.98  
% 3.68/0.98  ------ QBF Options
% 3.68/0.98  
% 3.68/0.98  --qbf_mode                              false
% 3.68/0.98  --qbf_elim_univ                         false
% 3.68/0.98  --qbf_dom_inst                          none
% 3.68/0.98  --qbf_dom_pre_inst                      false
% 3.68/0.98  --qbf_sk_in                             false
% 3.68/0.98  --qbf_pred_elim                         true
% 3.68/0.98  --qbf_split                             512
% 3.68/0.98  
% 3.68/0.98  ------ BMC1 Options
% 3.68/0.98  
% 3.68/0.98  --bmc1_incremental                      false
% 3.68/0.98  --bmc1_axioms                           reachable_all
% 3.68/0.98  --bmc1_min_bound                        0
% 3.68/0.98  --bmc1_max_bound                        -1
% 3.68/0.98  --bmc1_max_bound_default                -1
% 3.68/0.98  --bmc1_symbol_reachability              true
% 3.68/0.98  --bmc1_property_lemmas                  false
% 3.68/0.98  --bmc1_k_induction                      false
% 3.68/0.98  --bmc1_non_equiv_states                 false
% 3.68/0.98  --bmc1_deadlock                         false
% 3.68/0.98  --bmc1_ucm                              false
% 3.68/0.98  --bmc1_add_unsat_core                   none
% 3.68/0.98  --bmc1_unsat_core_children              false
% 3.68/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.68/0.98  --bmc1_out_stat                         full
% 3.68/0.98  --bmc1_ground_init                      false
% 3.68/0.98  --bmc1_pre_inst_next_state              false
% 3.68/0.98  --bmc1_pre_inst_state                   false
% 3.68/0.98  --bmc1_pre_inst_reach_state             false
% 3.68/0.98  --bmc1_out_unsat_core                   false
% 3.68/0.98  --bmc1_aig_witness_out                  false
% 3.68/0.98  --bmc1_verbose                          false
% 3.68/0.98  --bmc1_dump_clauses_tptp                false
% 3.68/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.68/0.98  --bmc1_dump_file                        -
% 3.68/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.68/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.68/0.98  --bmc1_ucm_extend_mode                  1
% 3.68/0.98  --bmc1_ucm_init_mode                    2
% 3.68/0.98  --bmc1_ucm_cone_mode                    none
% 3.68/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.68/0.98  --bmc1_ucm_relax_model                  4
% 3.68/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.68/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.68/0.98  --bmc1_ucm_layered_model                none
% 3.68/0.98  --bmc1_ucm_max_lemma_size               10
% 3.68/0.98  
% 3.68/0.98  ------ AIG Options
% 3.68/0.98  
% 3.68/0.98  --aig_mode                              false
% 3.68/0.98  
% 3.68/0.98  ------ Instantiation Options
% 3.68/0.98  
% 3.68/0.98  --instantiation_flag                    true
% 3.68/0.98  --inst_sos_flag                         false
% 3.68/0.98  --inst_sos_phase                        true
% 3.68/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.68/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.68/0.98  --inst_lit_sel_side                     none
% 3.68/0.98  --inst_solver_per_active                1400
% 3.68/0.98  --inst_solver_calls_frac                1.
% 3.68/0.98  --inst_passive_queue_type               priority_queues
% 3.68/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.68/0.98  --inst_passive_queues_freq              [25;2]
% 3.68/0.98  --inst_dismatching                      true
% 3.68/0.98  --inst_eager_unprocessed_to_passive     true
% 3.68/0.98  --inst_prop_sim_given                   true
% 3.68/0.98  --inst_prop_sim_new                     false
% 3.68/0.98  --inst_subs_new                         false
% 3.68/0.98  --inst_eq_res_simp                      false
% 3.68/0.98  --inst_subs_given                       false
% 3.68/0.98  --inst_orphan_elimination               true
% 3.68/0.98  --inst_learning_loop_flag               true
% 3.68/0.98  --inst_learning_start                   3000
% 3.68/0.98  --inst_learning_factor                  2
% 3.68/0.98  --inst_start_prop_sim_after_learn       3
% 3.68/0.98  --inst_sel_renew                        solver
% 3.68/0.98  --inst_lit_activity_flag                true
% 3.68/0.98  --inst_restr_to_given                   false
% 3.68/0.98  --inst_activity_threshold               500
% 3.68/0.98  --inst_out_proof                        true
% 3.68/0.98  
% 3.68/0.98  ------ Resolution Options
% 3.68/0.98  
% 3.68/0.98  --resolution_flag                       false
% 3.68/0.98  --res_lit_sel                           adaptive
% 3.68/0.98  --res_lit_sel_side                      none
% 3.68/0.98  --res_ordering                          kbo
% 3.68/0.98  --res_to_prop_solver                    active
% 3.68/0.98  --res_prop_simpl_new                    false
% 3.68/0.98  --res_prop_simpl_given                  true
% 3.68/0.98  --res_passive_queue_type                priority_queues
% 3.68/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.68/0.98  --res_passive_queues_freq               [15;5]
% 3.68/0.98  --res_forward_subs                      full
% 3.68/0.98  --res_backward_subs                     full
% 3.68/0.98  --res_forward_subs_resolution           true
% 3.68/0.98  --res_backward_subs_resolution          true
% 3.68/0.98  --res_orphan_elimination                true
% 3.68/0.98  --res_time_limit                        2.
% 3.68/0.98  --res_out_proof                         true
% 3.68/0.98  
% 3.68/0.98  ------ Superposition Options
% 3.68/0.98  
% 3.68/0.98  --superposition_flag                    true
% 3.68/0.98  --sup_passive_queue_type                priority_queues
% 3.68/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.68/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.68/0.98  --demod_completeness_check              fast
% 3.68/0.98  --demod_use_ground                      true
% 3.68/0.98  --sup_to_prop_solver                    passive
% 3.68/0.98  --sup_prop_simpl_new                    true
% 3.68/0.98  --sup_prop_simpl_given                  true
% 3.68/0.98  --sup_fun_splitting                     false
% 3.68/0.98  --sup_smt_interval                      50000
% 3.68/0.98  
% 3.68/0.98  ------ Superposition Simplification Setup
% 3.68/0.98  
% 3.68/0.98  --sup_indices_passive                   []
% 3.68/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.68/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.68/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.68/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.68/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.68/0.98  --sup_full_bw                           [BwDemod]
% 3.68/0.98  --sup_immed_triv                        [TrivRules]
% 3.68/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.68/0.98  --sup_immed_bw_main                     []
% 3.68/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.68/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.68/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.68/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.68/0.98  
% 3.68/0.98  ------ Combination Options
% 3.68/0.98  
% 3.68/0.98  --comb_res_mult                         3
% 3.68/0.98  --comb_sup_mult                         2
% 3.68/0.98  --comb_inst_mult                        10
% 3.68/0.98  
% 3.68/0.98  ------ Debug Options
% 3.68/0.98  
% 3.68/0.98  --dbg_backtrace                         false
% 3.68/0.98  --dbg_dump_prop_clauses                 false
% 3.68/0.98  --dbg_dump_prop_clauses_file            -
% 3.68/0.98  --dbg_out_stat                          false
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  ------ Proving...
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  % SZS status Theorem for theBenchmark.p
% 3.68/0.98  
% 3.68/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.68/0.98  
% 3.68/0.98  fof(f4,axiom,(
% 3.68/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f25,plain,(
% 3.68/0.98    ! [X0,X1,X2] : (m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 3.68/0.98    inference(ennf_transformation,[],[f4])).
% 3.68/0.98  
% 3.68/0.98  fof(f26,plain,(
% 3.68/0.98    ! [X0,X1,X2] : (m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 3.68/0.98    inference(flattening,[],[f25])).
% 3.68/0.98  
% 3.68/0.98  fof(f52,plain,(
% 3.68/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f26])).
% 3.68/0.98  
% 3.68/0.98  fof(f9,axiom,(
% 3.68/0.98    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f15,plain,(
% 3.68/0.98    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 3.68/0.98    inference(pure_predicate_removal,[],[f9])).
% 3.68/0.98  
% 3.68/0.98  fof(f18,plain,(
% 3.68/0.98    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 3.68/0.98    inference(pure_predicate_removal,[],[f15])).
% 3.68/0.98  
% 3.68/0.98  fof(f64,plain,(
% 3.68/0.98    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 3.68/0.98    inference(cnf_transformation,[],[f18])).
% 3.68/0.98  
% 3.68/0.98  fof(f8,axiom,(
% 3.68/0.98    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f17,plain,(
% 3.68/0.98    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 3.68/0.98    inference(pure_predicate_removal,[],[f8])).
% 3.68/0.98  
% 3.68/0.98  fof(f62,plain,(
% 3.68/0.98    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 3.68/0.98    inference(cnf_transformation,[],[f17])).
% 3.68/0.98  
% 3.68/0.98  fof(f11,axiom,(
% 3.68/0.98    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f66,plain,(
% 3.68/0.98    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 3.68/0.98    inference(cnf_transformation,[],[f11])).
% 3.68/0.98  
% 3.68/0.98  fof(f13,conjecture,(
% 3.68/0.98    ! [X0] : (~v1_xboole_0(X0) => (v1_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))))))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f14,negated_conjecture,(
% 3.68/0.98    ~! [X0] : (~v1_xboole_0(X0) => (v1_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))))))),
% 3.68/0.98    inference(negated_conjecture,[],[f13])).
% 3.68/0.98  
% 3.68/0.98  fof(f35,plain,(
% 3.68/0.98    ? [X0] : ((? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v1_lattice3(k2_yellow_1(X0))) & ~v1_xboole_0(X0))),
% 3.68/0.98    inference(ennf_transformation,[],[f14])).
% 3.68/0.98  
% 3.68/0.98  fof(f36,plain,(
% 3.68/0.98    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v1_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0))),
% 3.68/0.98    inference(flattening,[],[f35])).
% 3.68/0.98  
% 3.68/0.98  fof(f46,plain,(
% 3.68/0.98    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) => (~r1_tarski(k2_xboole_0(X1,sK3),k10_lattice3(k2_yellow_1(X0),X1,sK3)) & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0))))) )),
% 3.68/0.98    introduced(choice_axiom,[])).
% 3.68/0.98  
% 3.68/0.98  fof(f45,plain,(
% 3.68/0.98    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) => (? [X2] : (~r1_tarski(k2_xboole_0(sK2,X2),k10_lattice3(k2_yellow_1(X0),sK2,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(X0))))) )),
% 3.68/0.98    introduced(choice_axiom,[])).
% 3.68/0.98  
% 3.68/0.98  fof(f44,plain,(
% 3.68/0.98    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v1_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(sK1),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK1)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))) & v1_lattice3(k2_yellow_1(sK1)) & ~v1_xboole_0(sK1))),
% 3.68/0.98    introduced(choice_axiom,[])).
% 3.68/0.98  
% 3.68/0.98  fof(f47,plain,(
% 3.68/0.98    ((~r1_tarski(k2_xboole_0(sK2,sK3),k10_lattice3(k2_yellow_1(sK1),sK2,sK3)) & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))) & v1_lattice3(k2_yellow_1(sK1)) & ~v1_xboole_0(sK1)),
% 3.68/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f36,f46,f45,f44])).
% 3.68/0.98  
% 3.68/0.98  fof(f72,plain,(
% 3.68/0.98    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))),
% 3.68/0.98    inference(cnf_transformation,[],[f47])).
% 3.68/0.98  
% 3.68/0.98  fof(f73,plain,(
% 3.68/0.98    m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))),
% 3.68/0.98    inference(cnf_transformation,[],[f47])).
% 3.68/0.98  
% 3.68/0.98  fof(f6,axiom,(
% 3.68/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f29,plain,(
% 3.68/0.98    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 3.68/0.98    inference(ennf_transformation,[],[f6])).
% 3.68/0.98  
% 3.68/0.98  fof(f30,plain,(
% 3.68/0.98    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 3.68/0.98    inference(flattening,[],[f29])).
% 3.68/0.98  
% 3.68/0.98  fof(f60,plain,(
% 3.68/0.98    ( ! [X2,X0,X1] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f30])).
% 3.68/0.98  
% 3.68/0.98  fof(f71,plain,(
% 3.68/0.98    v1_lattice3(k2_yellow_1(sK1))),
% 3.68/0.98    inference(cnf_transformation,[],[f47])).
% 3.68/0.98  
% 3.68/0.98  fof(f5,axiom,(
% 3.68/0.98    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f27,plain,(
% 3.68/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 3.68/0.98    inference(ennf_transformation,[],[f5])).
% 3.68/0.98  
% 3.68/0.98  fof(f28,plain,(
% 3.68/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.68/0.98    inference(flattening,[],[f27])).
% 3.68/0.98  
% 3.68/0.98  fof(f38,plain,(
% 3.68/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3))) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.68/0.98    inference(nnf_transformation,[],[f28])).
% 3.68/0.98  
% 3.68/0.98  fof(f39,plain,(
% 3.68/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.68/0.98    inference(flattening,[],[f38])).
% 3.68/0.98  
% 3.68/0.98  fof(f40,plain,(
% 3.68/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.68/0.98    inference(rectify,[],[f39])).
% 3.68/0.98  
% 3.68/0.98  fof(f41,plain,(
% 3.68/0.98    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,X3,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))))),
% 3.68/0.98    introduced(choice_axiom,[])).
% 3.68/0.98  
% 3.68/0.98  fof(f42,plain,(
% 3.68/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,X3,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.68/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).
% 3.68/0.98  
% 3.68/0.98  fof(f53,plain,(
% 3.68/0.98    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X1,X3) | k10_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f42])).
% 3.68/0.98  
% 3.68/0.98  fof(f77,plain,(
% 3.68/0.98    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.68/0.98    inference(equality_resolution,[],[f53])).
% 3.68/0.98  
% 3.68/0.98  fof(f3,axiom,(
% 3.68/0.98    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f23,plain,(
% 3.68/0.98    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 3.68/0.98    inference(ennf_transformation,[],[f3])).
% 3.68/0.98  
% 3.68/0.98  fof(f24,plain,(
% 3.68/0.98    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 3.68/0.98    inference(flattening,[],[f23])).
% 3.68/0.98  
% 3.68/0.98  fof(f51,plain,(
% 3.68/0.98    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f24])).
% 3.68/0.98  
% 3.68/0.98  fof(f2,axiom,(
% 3.68/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f21,plain,(
% 3.68/0.98    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.68/0.98    inference(ennf_transformation,[],[f2])).
% 3.68/0.98  
% 3.68/0.98  fof(f22,plain,(
% 3.68/0.98    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.68/0.98    inference(flattening,[],[f21])).
% 3.68/0.98  
% 3.68/0.98  fof(f37,plain,(
% 3.68/0.98    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.68/0.98    inference(nnf_transformation,[],[f22])).
% 3.68/0.98  
% 3.68/0.98  fof(f50,plain,(
% 3.68/0.98    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f37])).
% 3.68/0.98  
% 3.68/0.98  fof(f63,plain,(
% 3.68/0.98    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 3.68/0.98    inference(cnf_transformation,[],[f18])).
% 3.68/0.98  
% 3.68/0.98  fof(f12,axiom,(
% 3.68/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f34,plain,(
% 3.68/0.98    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 3.68/0.98    inference(ennf_transformation,[],[f12])).
% 3.68/0.98  
% 3.68/0.98  fof(f43,plain,(
% 3.68/0.98    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 3.68/0.98    inference(nnf_transformation,[],[f34])).
% 3.68/0.98  
% 3.68/0.98  fof(f68,plain,(
% 3.68/0.98    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f43])).
% 3.68/0.98  
% 3.68/0.98  fof(f70,plain,(
% 3.68/0.98    ~v1_xboole_0(sK1)),
% 3.68/0.98    inference(cnf_transformation,[],[f47])).
% 3.68/0.98  
% 3.68/0.98  fof(f1,axiom,(
% 3.68/0.98    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f19,plain,(
% 3.68/0.98    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 3.68/0.98    inference(ennf_transformation,[],[f1])).
% 3.68/0.98  
% 3.68/0.98  fof(f20,plain,(
% 3.68/0.98    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 3.68/0.98    inference(flattening,[],[f19])).
% 3.68/0.98  
% 3.68/0.98  fof(f48,plain,(
% 3.68/0.98    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f20])).
% 3.68/0.98  
% 3.68/0.98  fof(f74,plain,(
% 3.68/0.98    ~r1_tarski(k2_xboole_0(sK2,sK3),k10_lattice3(k2_yellow_1(sK1),sK2,sK3))),
% 3.68/0.98    inference(cnf_transformation,[],[f47])).
% 3.68/0.98  
% 3.68/0.98  fof(f7,axiom,(
% 3.68/0.98    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1))))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f31,plain,(
% 3.68/0.98    ! [X0] : (! [X1] : (! [X2] : (k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 3.68/0.98    inference(ennf_transformation,[],[f7])).
% 3.68/0.98  
% 3.68/0.98  fof(f32,plain,(
% 3.68/0.98    ! [X0] : (! [X1] : (! [X2] : (k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 3.68/0.98    inference(flattening,[],[f31])).
% 3.68/0.98  
% 3.68/0.98  fof(f61,plain,(
% 3.68/0.98    ( ! [X2,X0,X1] : (k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f32])).
% 3.68/0.98  
% 3.68/0.98  cnf(c_4,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.68/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.68/0.98      | m1_subset_1(k13_lattice3(X1,X2,X0),u1_struct_0(X1))
% 3.68/0.98      | ~ v5_orders_2(X1)
% 3.68/0.98      | ~ v1_lattice3(X1)
% 3.68/0.98      | ~ l1_orders_2(X1) ),
% 3.68/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_15,plain,
% 3.68/0.98      ( v5_orders_2(k2_yellow_1(X0)) ),
% 3.68/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_907,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.68/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.68/0.98      | m1_subset_1(k13_lattice3(X1,X2,X0),u1_struct_0(X1))
% 3.68/0.98      | ~ v1_lattice3(X1)
% 3.68/0.98      | ~ l1_orders_2(X1)
% 3.68/0.98      | k2_yellow_1(X3) != X1 ),
% 3.68/0.98      inference(resolution_lifted,[status(thm)],[c_4,c_15]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_908,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
% 3.68/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
% 3.68/0.98      | m1_subset_1(k13_lattice3(k2_yellow_1(X1),X0,X2),u1_struct_0(k2_yellow_1(X1)))
% 3.68/0.98      | ~ v1_lattice3(k2_yellow_1(X1))
% 3.68/0.98      | ~ l1_orders_2(k2_yellow_1(X1)) ),
% 3.68/0.98      inference(unflattening,[status(thm)],[c_907]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_14,plain,
% 3.68/0.98      ( l1_orders_2(k2_yellow_1(X0)) ),
% 3.68/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_922,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
% 3.68/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
% 3.68/0.98      | m1_subset_1(k13_lattice3(k2_yellow_1(X1),X2,X0),u1_struct_0(k2_yellow_1(X1)))
% 3.68/0.98      | ~ v1_lattice3(k2_yellow_1(X1)) ),
% 3.68/0.98      inference(forward_subsumption_resolution,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_908,c_14]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2718,plain,
% 3.68/0.98      ( m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) != iProver_top
% 3.68/0.98      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) != iProver_top
% 3.68/0.98      | m1_subset_1(k13_lattice3(k2_yellow_1(X1),X2,X0),u1_struct_0(k2_yellow_1(X1))) = iProver_top
% 3.68/0.98      | v1_lattice3(k2_yellow_1(X1)) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_922]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_19,plain,
% 3.68/0.98      ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
% 3.68/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2753,plain,
% 3.68/0.98      ( m1_subset_1(X0,X1) != iProver_top
% 3.68/0.98      | m1_subset_1(X2,X1) != iProver_top
% 3.68/0.98      | m1_subset_1(k13_lattice3(k2_yellow_1(X1),X2,X0),X1) = iProver_top
% 3.68/0.98      | v1_lattice3(k2_yellow_1(X1)) != iProver_top ),
% 3.68/0.98      inference(demodulation,[status(thm)],[c_2718,c_19]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_24,negated_conjecture,
% 3.68/0.98      ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
% 3.68/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2729,plain,
% 3.68/0.98      ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2739,plain,
% 3.68/0.98      ( m1_subset_1(sK2,sK1) = iProver_top ),
% 3.68/0.98      inference(demodulation,[status(thm)],[c_2729,c_19]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_23,negated_conjecture,
% 3.68/0.98      ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) ),
% 3.68/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2730,plain,
% 3.68/0.98      ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2742,plain,
% 3.68/0.98      ( m1_subset_1(sK3,sK1) = iProver_top ),
% 3.68/0.98      inference(demodulation,[status(thm)],[c_2730,c_19]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_12,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.68/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.68/0.98      | ~ v5_orders_2(X1)
% 3.68/0.98      | ~ v1_lattice3(X1)
% 3.68/0.98      | ~ l1_orders_2(X1)
% 3.68/0.98      | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0) ),
% 3.68/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_884,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.68/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.68/0.98      | ~ v1_lattice3(X1)
% 3.68/0.98      | ~ l1_orders_2(X1)
% 3.68/0.98      | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0)
% 3.68/0.98      | k2_yellow_1(X3) != X1 ),
% 3.68/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_15]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_885,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
% 3.68/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
% 3.68/0.98      | ~ v1_lattice3(k2_yellow_1(X1))
% 3.68/0.98      | ~ l1_orders_2(k2_yellow_1(X1))
% 3.68/0.98      | k10_lattice3(k2_yellow_1(X1),X0,X2) = k13_lattice3(k2_yellow_1(X1),X0,X2) ),
% 3.68/0.98      inference(unflattening,[status(thm)],[c_884]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_899,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
% 3.68/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
% 3.68/0.98      | ~ v1_lattice3(k2_yellow_1(X1))
% 3.68/0.98      | k10_lattice3(k2_yellow_1(X1),X2,X0) = k13_lattice3(k2_yellow_1(X1),X2,X0) ),
% 3.68/0.98      inference(forward_subsumption_resolution,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_885,c_14]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2719,plain,
% 3.68/0.98      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k13_lattice3(k2_yellow_1(X0),X1,X2)
% 3.68/0.98      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.68/0.98      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.68/0.98      | v1_lattice3(k2_yellow_1(X0)) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_899]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2762,plain,
% 3.68/0.98      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k13_lattice3(k2_yellow_1(X0),X1,X2)
% 3.68/0.98      | m1_subset_1(X2,X0) != iProver_top
% 3.68/0.98      | m1_subset_1(X1,X0) != iProver_top
% 3.68/0.98      | v1_lattice3(k2_yellow_1(X0)) != iProver_top ),
% 3.68/0.98      inference(light_normalisation,[status(thm)],[c_2719,c_19]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3778,plain,
% 3.68/0.98      ( k10_lattice3(k2_yellow_1(sK1),X0,sK3) = k13_lattice3(k2_yellow_1(sK1),X0,sK3)
% 3.68/0.98      | m1_subset_1(X0,sK1) != iProver_top
% 3.68/0.98      | v1_lattice3(k2_yellow_1(sK1)) != iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_2742,c_2762]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_25,negated_conjecture,
% 3.68/0.98      ( v1_lattice3(k2_yellow_1(sK1)) ),
% 3.68/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_28,plain,
% 3.68/0.98      ( v1_lattice3(k2_yellow_1(sK1)) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_4431,plain,
% 3.68/0.98      ( m1_subset_1(X0,sK1) != iProver_top
% 3.68/0.98      | k10_lattice3(k2_yellow_1(sK1),X0,sK3) = k13_lattice3(k2_yellow_1(sK1),X0,sK3) ),
% 3.68/0.98      inference(global_propositional_subsumption,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_3778,c_28]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_4432,plain,
% 3.68/0.98      ( k10_lattice3(k2_yellow_1(sK1),X0,sK3) = k13_lattice3(k2_yellow_1(sK1),X0,sK3)
% 3.68/0.98      | m1_subset_1(X0,sK1) != iProver_top ),
% 3.68/0.98      inference(renaming,[status(thm)],[c_4431]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_4439,plain,
% 3.68/0.98      ( k10_lattice3(k2_yellow_1(sK1),sK2,sK3) = k13_lattice3(k2_yellow_1(sK1),sK2,sK3) ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_2739,c_4432]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_11,plain,
% 3.68/0.98      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 3.68/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.68/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.68/0.98      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 3.68/0.98      | ~ v5_orders_2(X0)
% 3.68/0.98      | ~ v1_lattice3(X0)
% 3.68/0.98      | v2_struct_0(X0)
% 3.68/0.98      | ~ l1_orders_2(X0) ),
% 3.68/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3,plain,
% 3.68/0.98      ( ~ v1_lattice3(X0) | ~ v2_struct_0(X0) | ~ l1_orders_2(X0) ),
% 3.68/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_154,plain,
% 3.68/0.98      ( ~ v1_lattice3(X0)
% 3.68/0.98      | ~ v5_orders_2(X0)
% 3.68/0.98      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 3.68/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.68/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.68/0.98      | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 3.68/0.98      | ~ l1_orders_2(X0) ),
% 3.68/0.98      inference(global_propositional_subsumption,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_11,c_3]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_155,plain,
% 3.68/0.98      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 3.68/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.68/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.68/0.98      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 3.68/0.98      | ~ v5_orders_2(X0)
% 3.68/0.98      | ~ v1_lattice3(X0)
% 3.68/0.98      | ~ l1_orders_2(X0) ),
% 3.68/0.98      inference(renaming,[status(thm)],[c_154]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_838,plain,
% 3.68/0.98      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
% 3.68/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.68/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.68/0.98      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
% 3.68/0.98      | ~ v1_lattice3(X0)
% 3.68/0.98      | ~ l1_orders_2(X0)
% 3.68/0.98      | k2_yellow_1(X3) != X0 ),
% 3.68/0.98      inference(resolution_lifted,[status(thm)],[c_155,c_15]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_839,plain,
% 3.68/0.98      ( r1_orders_2(k2_yellow_1(X0),X1,k10_lattice3(k2_yellow_1(X0),X1,X2))
% 3.68/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.68/0.98      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.68/0.98      | ~ m1_subset_1(k10_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
% 3.68/0.98      | ~ v1_lattice3(k2_yellow_1(X0))
% 3.68/0.98      | ~ l1_orders_2(k2_yellow_1(X0)) ),
% 3.68/0.98      inference(unflattening,[status(thm)],[c_838]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_841,plain,
% 3.68/0.98      ( ~ v1_lattice3(k2_yellow_1(X0))
% 3.68/0.98      | ~ m1_subset_1(k10_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
% 3.68/0.98      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.68/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.68/0.98      | r1_orders_2(k2_yellow_1(X0),X1,k10_lattice3(k2_yellow_1(X0),X1,X2)) ),
% 3.68/0.98      inference(global_propositional_subsumption,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_839,c_14]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_842,plain,
% 3.68/0.98      ( r1_orders_2(k2_yellow_1(X0),X1,k10_lattice3(k2_yellow_1(X0),X1,X2))
% 3.68/0.98      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.68/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.68/0.98      | ~ m1_subset_1(k10_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
% 3.68/0.98      | ~ v1_lattice3(k2_yellow_1(X0)) ),
% 3.68/0.98      inference(renaming,[status(thm)],[c_841]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2721,plain,
% 3.68/0.98      ( r1_orders_2(k2_yellow_1(X0),X1,k10_lattice3(k2_yellow_1(X0),X1,X2)) = iProver_top
% 3.68/0.98      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.68/0.98      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.68/0.98      | m1_subset_1(k10_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.68/0.98      | v1_lattice3(k2_yellow_1(X0)) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_842]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2780,plain,
% 3.68/0.98      ( r1_orders_2(k2_yellow_1(X0),X1,k10_lattice3(k2_yellow_1(X0),X1,X2)) = iProver_top
% 3.68/0.98      | m1_subset_1(X2,X0) != iProver_top
% 3.68/0.98      | m1_subset_1(X1,X0) != iProver_top
% 3.68/0.98      | m1_subset_1(k10_lattice3(k2_yellow_1(X0),X1,X2),X0) != iProver_top
% 3.68/0.98      | v1_lattice3(k2_yellow_1(X0)) != iProver_top ),
% 3.68/0.98      inference(light_normalisation,[status(thm)],[c_2721,c_19]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1,plain,
% 3.68/0.98      ( ~ r1_orders_2(X0,X1,X2)
% 3.68/0.98      | r3_orders_2(X0,X1,X2)
% 3.68/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.68/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.68/0.98      | v2_struct_0(X0)
% 3.68/0.98      | ~ v3_orders_2(X0)
% 3.68/0.98      | ~ l1_orders_2(X0) ),
% 3.68/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_16,plain,
% 3.68/0.98      ( v3_orders_2(k2_yellow_1(X0)) ),
% 3.68/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_404,plain,
% 3.68/0.98      ( ~ r1_orders_2(X0,X1,X2)
% 3.68/0.98      | r3_orders_2(X0,X1,X2)
% 3.68/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.68/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.68/0.98      | v2_struct_0(X0)
% 3.68/0.98      | ~ l1_orders_2(X0)
% 3.68/0.98      | k2_yellow_1(X3) != X0 ),
% 3.68/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_16]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_405,plain,
% 3.68/0.98      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 3.68/0.98      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.68/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.68/0.98      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.68/0.98      | v2_struct_0(k2_yellow_1(X0))
% 3.68/0.98      | ~ l1_orders_2(k2_yellow_1(X0)) ),
% 3.68/0.98      inference(unflattening,[status(thm)],[c_404]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_409,plain,
% 3.68/0.98      ( v2_struct_0(k2_yellow_1(X0))
% 3.68/0.98      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.68/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.68/0.98      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.68/0.98      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2) ),
% 3.68/0.98      inference(global_propositional_subsumption,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_405,c_14]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_410,plain,
% 3.68/0.98      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 3.68/0.98      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.68/0.98      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.68/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.68/0.98      | v2_struct_0(k2_yellow_1(X0)) ),
% 3.68/0.98      inference(renaming,[status(thm)],[c_409]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_21,plain,
% 3.68/0.98      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.68/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.68/0.98      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.68/0.98      | r1_tarski(X1,X2)
% 3.68/0.98      | v1_xboole_0(X0) ),
% 3.68/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_26,negated_conjecture,
% 3.68/0.98      ( ~ v1_xboole_0(sK1) ),
% 3.68/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_322,plain,
% 3.68/0.98      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.68/0.98      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.68/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.68/0.98      | r1_tarski(X1,X2)
% 3.68/0.98      | sK1 != X0 ),
% 3.68/0.98      inference(resolution_lifted,[status(thm)],[c_21,c_26]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_323,plain,
% 3.68/0.98      ( ~ r3_orders_2(k2_yellow_1(sK1),X0,X1)
% 3.68/0.98      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
% 3.68/0.98      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 3.68/0.98      | r1_tarski(X0,X1) ),
% 3.68/0.98      inference(unflattening,[status(thm)],[c_322]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1649,plain,
% 3.68/0.98      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 3.68/0.98      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.68/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.68/0.98      | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK1)))
% 3.68/0.98      | ~ m1_subset_1(X4,u1_struct_0(k2_yellow_1(sK1)))
% 3.68/0.98      | r1_tarski(X4,X3)
% 3.68/0.98      | v2_struct_0(k2_yellow_1(X0))
% 3.68/0.98      | X4 != X1
% 3.68/0.98      | X3 != X2
% 3.68/0.98      | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
% 3.68/0.98      inference(resolution_lifted,[status(thm)],[c_410,c_323]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1650,plain,
% 3.68/0.98      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 3.68/0.98      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.68/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.68/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK1)))
% 3.68/0.98      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
% 3.68/0.98      | r1_tarski(X1,X2)
% 3.68/0.98      | v2_struct_0(k2_yellow_1(X0))
% 3.68/0.98      | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
% 3.68/0.98      inference(unflattening,[status(thm)],[c_1649]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_559,plain,
% 3.68/0.98      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 3.68/0.98      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.68/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.68/0.98      | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK1)))
% 3.68/0.98      | ~ m1_subset_1(X4,u1_struct_0(k2_yellow_1(sK1)))
% 3.68/0.98      | r1_tarski(X4,X3)
% 3.68/0.98      | v2_struct_0(k2_yellow_1(X0))
% 3.68/0.98      | X4 != X1
% 3.68/0.98      | X3 != X2
% 3.68/0.98      | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
% 3.68/0.98      inference(resolution_lifted,[status(thm)],[c_410,c_323]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_560,plain,
% 3.68/0.98      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 3.68/0.98      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.68/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.68/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK1)))
% 3.68/0.98      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
% 3.68/0.98      | r1_tarski(X1,X2)
% 3.68/0.98      | v2_struct_0(k2_yellow_1(X0))
% 3.68/0.98      | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
% 3.68/0.98      inference(unflattening,[status(thm)],[c_559]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1002,plain,
% 3.68/0.98      ( ~ v1_lattice3(X0) | ~ v2_struct_0(X0) | k2_yellow_1(X1) != X0 ),
% 3.68/0.98      inference(resolution_lifted,[status(thm)],[c_3,c_14]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1003,plain,
% 3.68/0.98      ( ~ v1_lattice3(k2_yellow_1(X0)) | ~ v2_struct_0(k2_yellow_1(X0)) ),
% 3.68/0.98      inference(unflattening,[status(thm)],[c_1002]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1107,plain,
% 3.68/0.98      ( ~ v2_struct_0(k2_yellow_1(X0))
% 3.68/0.98      | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
% 3.68/0.98      inference(resolution_lifted,[status(thm)],[c_25,c_1003]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1652,plain,
% 3.68/0.98      ( r1_tarski(X1,X2)
% 3.68/0.98      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
% 3.68/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK1)))
% 3.68/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.68/0.98      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.68/0.98      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 3.68/0.98      | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
% 3.68/0.98      inference(global_propositional_subsumption,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_1650,c_560,c_1107]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1653,plain,
% 3.68/0.98      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 3.68/0.98      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.68/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.68/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK1)))
% 3.68/0.98      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
% 3.68/0.98      | r1_tarski(X1,X2)
% 3.68/0.98      | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
% 3.68/0.98      inference(renaming,[status(thm)],[c_1652]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2717,plain,
% 3.68/0.98      ( k2_yellow_1(X0) != k2_yellow_1(sK1)
% 3.68/0.98      | r1_orders_2(k2_yellow_1(X0),X1,X2) != iProver_top
% 3.68/0.98      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.68/0.98      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.68/0.98      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
% 3.68/0.98      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
% 3.68/0.98      | r1_tarski(X1,X2) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_1653]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2818,plain,
% 3.68/0.98      ( k2_yellow_1(X0) != k2_yellow_1(sK1)
% 3.68/0.98      | r1_orders_2(k2_yellow_1(X0),X1,X2) != iProver_top
% 3.68/0.98      | m1_subset_1(X2,X0) != iProver_top
% 3.68/0.98      | m1_subset_1(X1,X0) != iProver_top
% 3.68/0.98      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
% 3.68/0.98      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
% 3.68/0.98      | r1_tarski(X1,X2) = iProver_top ),
% 3.68/0.98      inference(light_normalisation,[status(thm)],[c_2717,c_19]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2819,plain,
% 3.68/0.98      ( k2_yellow_1(X0) != k2_yellow_1(sK1)
% 3.68/0.98      | r1_orders_2(k2_yellow_1(X0),X1,X2) != iProver_top
% 3.68/0.98      | m1_subset_1(X2,X0) != iProver_top
% 3.68/0.98      | m1_subset_1(X1,X0) != iProver_top
% 3.68/0.98      | m1_subset_1(X1,sK1) != iProver_top
% 3.68/0.98      | m1_subset_1(X2,sK1) != iProver_top
% 3.68/0.98      | r1_tarski(X1,X2) = iProver_top ),
% 3.68/0.98      inference(demodulation,[status(thm)],[c_2818,c_19]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3140,plain,
% 3.68/0.98      ( r1_orders_2(k2_yellow_1(sK1),X0,X1) != iProver_top
% 3.68/0.98      | m1_subset_1(X1,sK1) != iProver_top
% 3.68/0.98      | m1_subset_1(X0,sK1) != iProver_top
% 3.68/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.68/0.98      inference(equality_resolution,[status(thm)],[c_2819]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_4735,plain,
% 3.68/0.98      ( m1_subset_1(X0,sK1) != iProver_top
% 3.68/0.98      | m1_subset_1(X1,sK1) != iProver_top
% 3.68/0.98      | m1_subset_1(k10_lattice3(k2_yellow_1(sK1),X0,X1),sK1) != iProver_top
% 3.68/0.98      | r1_tarski(X0,k10_lattice3(k2_yellow_1(sK1),X0,X1)) = iProver_top
% 3.68/0.98      | v1_lattice3(k2_yellow_1(sK1)) != iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_2780,c_3140]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_8839,plain,
% 3.68/0.98      ( r1_tarski(X0,k10_lattice3(k2_yellow_1(sK1),X0,X1)) = iProver_top
% 3.68/0.98      | m1_subset_1(k10_lattice3(k2_yellow_1(sK1),X0,X1),sK1) != iProver_top
% 3.68/0.98      | m1_subset_1(X1,sK1) != iProver_top
% 3.68/0.98      | m1_subset_1(X0,sK1) != iProver_top ),
% 3.68/0.98      inference(global_propositional_subsumption,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_4735,c_28]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_8840,plain,
% 3.68/0.98      ( m1_subset_1(X0,sK1) != iProver_top
% 3.68/0.98      | m1_subset_1(X1,sK1) != iProver_top
% 3.68/0.98      | m1_subset_1(k10_lattice3(k2_yellow_1(sK1),X1,X0),sK1) != iProver_top
% 3.68/0.98      | r1_tarski(X1,k10_lattice3(k2_yellow_1(sK1),X1,X0)) = iProver_top ),
% 3.68/0.98      inference(renaming,[status(thm)],[c_8839]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_8849,plain,
% 3.68/0.98      ( m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),sK1) != iProver_top
% 3.68/0.98      | m1_subset_1(sK3,sK1) != iProver_top
% 3.68/0.98      | m1_subset_1(sK2,sK1) != iProver_top
% 3.68/0.98      | r1_tarski(sK2,k10_lattice3(k2_yellow_1(sK1),sK2,sK3)) = iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_4439,c_8840]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_8964,plain,
% 3.68/0.98      ( m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),sK1) != iProver_top
% 3.68/0.98      | m1_subset_1(sK3,sK1) != iProver_top
% 3.68/0.98      | m1_subset_1(sK2,sK1) != iProver_top
% 3.68/0.98      | r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3)) = iProver_top ),
% 3.68/0.98      inference(light_normalisation,[status(thm)],[c_8849,c_4439]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_0,plain,
% 3.68/0.98      ( ~ r1_tarski(X0,X1)
% 3.68/0.98      | ~ r1_tarski(X2,X1)
% 3.68/0.98      | r1_tarski(k2_xboole_0(X2,X0),X1) ),
% 3.68/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2732,plain,
% 3.68/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.68/0.98      | r1_tarski(X2,X1) != iProver_top
% 3.68/0.98      | r1_tarski(k2_xboole_0(X2,X0),X1) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_22,negated_conjecture,
% 3.68/0.98      ( ~ r1_tarski(k2_xboole_0(sK2,sK3),k10_lattice3(k2_yellow_1(sK1),sK2,sK3)) ),
% 3.68/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2731,plain,
% 3.68/0.98      ( r1_tarski(k2_xboole_0(sK2,sK3),k10_lattice3(k2_yellow_1(sK1),sK2,sK3)) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3705,plain,
% 3.68/0.98      ( r1_tarski(sK3,k10_lattice3(k2_yellow_1(sK1),sK2,sK3)) != iProver_top
% 3.68/0.98      | r1_tarski(sK2,k10_lattice3(k2_yellow_1(sK1),sK2,sK3)) != iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_2732,c_2731]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_4458,plain,
% 3.68/0.98      ( r1_tarski(sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3)) != iProver_top
% 3.68/0.98      | r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3)) != iProver_top ),
% 3.68/0.98      inference(demodulation,[status(thm)],[c_4439,c_3705]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_13,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.68/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.68/0.98      | ~ v5_orders_2(X1)
% 3.68/0.98      | ~ v1_lattice3(X1)
% 3.68/0.98      | ~ l1_orders_2(X1)
% 3.68/0.98      | k10_lattice3(X1,X0,X2) = k10_lattice3(X1,X2,X0) ),
% 3.68/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_861,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.68/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.68/0.98      | ~ v1_lattice3(X1)
% 3.68/0.98      | ~ l1_orders_2(X1)
% 3.68/0.98      | k10_lattice3(X1,X0,X2) = k10_lattice3(X1,X2,X0)
% 3.68/0.98      | k2_yellow_1(X3) != X1 ),
% 3.68/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_15]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_862,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
% 3.68/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
% 3.68/0.98      | ~ v1_lattice3(k2_yellow_1(X1))
% 3.68/0.98      | ~ l1_orders_2(k2_yellow_1(X1))
% 3.68/0.98      | k10_lattice3(k2_yellow_1(X1),X2,X0) = k10_lattice3(k2_yellow_1(X1),X0,X2) ),
% 3.68/0.98      inference(unflattening,[status(thm)],[c_861]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_876,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
% 3.68/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
% 3.68/0.98      | ~ v1_lattice3(k2_yellow_1(X1))
% 3.68/0.98      | k10_lattice3(k2_yellow_1(X1),X0,X2) = k10_lattice3(k2_yellow_1(X1),X2,X0) ),
% 3.68/0.98      inference(forward_subsumption_resolution,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_862,c_14]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2720,plain,
% 3.68/0.98      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k10_lattice3(k2_yellow_1(X0),X2,X1)
% 3.68/0.98      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.68/0.98      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.68/0.98      | v1_lattice3(k2_yellow_1(X0)) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_876]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2771,plain,
% 3.68/0.98      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k10_lattice3(k2_yellow_1(X0),X2,X1)
% 3.68/0.98      | m1_subset_1(X1,X0) != iProver_top
% 3.68/0.98      | m1_subset_1(X2,X0) != iProver_top
% 3.68/0.98      | v1_lattice3(k2_yellow_1(X0)) != iProver_top ),
% 3.68/0.98      inference(light_normalisation,[status(thm)],[c_2720,c_19]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_4481,plain,
% 3.68/0.98      ( k10_lattice3(k2_yellow_1(sK1),X0,sK2) = k10_lattice3(k2_yellow_1(sK1),sK2,X0)
% 3.68/0.98      | m1_subset_1(X0,sK1) != iProver_top
% 3.68/0.98      | v1_lattice3(k2_yellow_1(sK1)) != iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_2739,c_2771]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_5165,plain,
% 3.68/0.98      ( m1_subset_1(X0,sK1) != iProver_top
% 3.68/0.98      | k10_lattice3(k2_yellow_1(sK1),X0,sK2) = k10_lattice3(k2_yellow_1(sK1),sK2,X0) ),
% 3.68/0.98      inference(global_propositional_subsumption,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_4481,c_28]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_5166,plain,
% 3.68/0.98      ( k10_lattice3(k2_yellow_1(sK1),X0,sK2) = k10_lattice3(k2_yellow_1(sK1),sK2,X0)
% 3.68/0.98      | m1_subset_1(X0,sK1) != iProver_top ),
% 3.68/0.98      inference(renaming,[status(thm)],[c_5165]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_5174,plain,
% 3.68/0.98      ( k10_lattice3(k2_yellow_1(sK1),sK3,sK2) = k10_lattice3(k2_yellow_1(sK1),sK2,sK3) ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_2742,c_5166]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3777,plain,
% 3.68/0.98      ( k10_lattice3(k2_yellow_1(sK1),X0,sK2) = k13_lattice3(k2_yellow_1(sK1),X0,sK2)
% 3.68/0.98      | m1_subset_1(X0,sK1) != iProver_top
% 3.68/0.98      | v1_lattice3(k2_yellow_1(sK1)) != iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_2739,c_2762]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3815,plain,
% 3.68/0.98      ( m1_subset_1(X0,sK1) != iProver_top
% 3.68/0.98      | k10_lattice3(k2_yellow_1(sK1),X0,sK2) = k13_lattice3(k2_yellow_1(sK1),X0,sK2) ),
% 3.68/0.98      inference(global_propositional_subsumption,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_3777,c_28]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3816,plain,
% 3.68/0.98      ( k10_lattice3(k2_yellow_1(sK1),X0,sK2) = k13_lattice3(k2_yellow_1(sK1),X0,sK2)
% 3.68/0.98      | m1_subset_1(X0,sK1) != iProver_top ),
% 3.68/0.98      inference(renaming,[status(thm)],[c_3815]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3824,plain,
% 3.68/0.98      ( k10_lattice3(k2_yellow_1(sK1),sK3,sK2) = k13_lattice3(k2_yellow_1(sK1),sK3,sK2) ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_2742,c_3816]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_5202,plain,
% 3.68/0.98      ( k13_lattice3(k2_yellow_1(sK1),sK3,sK2) = k13_lattice3(k2_yellow_1(sK1),sK2,sK3) ),
% 3.68/0.98      inference(light_normalisation,[status(thm)],[c_5174,c_3824,c_4439]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_5464,plain,
% 3.68/0.98      ( k10_lattice3(k2_yellow_1(sK1),sK3,sK2) = k13_lattice3(k2_yellow_1(sK1),sK2,sK3) ),
% 3.68/0.98      inference(demodulation,[status(thm)],[c_5202,c_3824]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_8851,plain,
% 3.68/0.98      ( m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),sK1) != iProver_top
% 3.68/0.98      | m1_subset_1(sK3,sK1) != iProver_top
% 3.68/0.98      | m1_subset_1(sK2,sK1) != iProver_top
% 3.68/0.98      | r1_tarski(sK3,k10_lattice3(k2_yellow_1(sK1),sK3,sK2)) = iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_5464,c_8840]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_8951,plain,
% 3.68/0.98      ( m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),sK1) != iProver_top
% 3.68/0.98      | m1_subset_1(sK3,sK1) != iProver_top
% 3.68/0.98      | m1_subset_1(sK2,sK1) != iProver_top
% 3.68/0.98      | r1_tarski(sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3)) = iProver_top ),
% 3.68/0.98      inference(light_normalisation,[status(thm)],[c_8851,c_5464]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_9717,plain,
% 3.68/0.98      ( m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),sK1) != iProver_top ),
% 3.68/0.98      inference(global_propositional_subsumption,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_8964,c_2739,c_2742,c_4458,c_8951]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_9722,plain,
% 3.68/0.98      ( m1_subset_1(sK3,sK1) != iProver_top
% 3.68/0.98      | m1_subset_1(sK2,sK1) != iProver_top
% 3.68/0.98      | v1_lattice3(k2_yellow_1(sK1)) != iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_2753,c_9717]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(contradiction,plain,
% 3.68/0.98      ( $false ),
% 3.68/0.98      inference(minisat,[status(thm)],[c_9722,c_2742,c_2739,c_28]) ).
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.68/0.98  
% 3.68/0.98  ------                               Statistics
% 3.68/0.98  
% 3.68/0.98  ------ General
% 3.68/0.98  
% 3.68/0.98  abstr_ref_over_cycles:                  0
% 3.68/0.98  abstr_ref_under_cycles:                 0
% 3.68/0.98  gc_basic_clause_elim:                   0
% 3.68/0.98  forced_gc_time:                         0
% 3.68/0.98  parsing_time:                           0.011
% 3.68/0.98  unif_index_cands_time:                  0.
% 3.68/0.98  unif_index_add_time:                    0.
% 3.68/0.98  orderings_time:                         0.
% 3.68/0.98  out_proof_time:                         0.012
% 3.68/0.98  total_time:                             0.312
% 3.68/0.98  num_of_symbols:                         52
% 3.68/0.98  num_of_terms:                           8257
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing
% 3.68/0.98  
% 3.68/0.98  num_of_splits:                          0
% 3.68/0.98  num_of_split_atoms:                     0
% 3.68/0.98  num_of_reused_defs:                     0
% 3.68/0.98  num_eq_ax_congr_red:                    31
% 3.68/0.98  num_of_sem_filtered_clauses:            1
% 3.68/0.98  num_of_subtypes:                        0
% 3.68/0.98  monotx_restored_types:                  0
% 3.68/0.98  sat_num_of_epr_types:                   0
% 3.68/0.98  sat_num_of_non_cyclic_types:            0
% 3.68/0.98  sat_guarded_non_collapsed_types:        0
% 3.68/0.98  num_pure_diseq_elim:                    0
% 3.68/0.98  simp_replaced_by:                       0
% 3.68/0.98  res_preprocessed:                       134
% 3.68/0.98  prep_upred:                             0
% 3.68/0.98  prep_unflattend:                        26
% 3.68/0.98  smt_new_axioms:                         0
% 3.68/0.98  pred_elim_cands:                        4
% 3.68/0.98  pred_elim:                              6
% 3.68/0.98  pred_elim_cl:                           8
% 3.68/0.98  pred_elim_cycles:                       13
% 3.68/0.98  merged_defs:                            0
% 3.68/0.98  merged_defs_ncl:                        0
% 3.68/0.98  bin_hyper_res:                          0
% 3.68/0.98  prep_cycles:                            5
% 3.68/0.98  pred_elim_time:                         0.031
% 3.68/0.98  splitting_time:                         0.
% 3.68/0.98  sem_filter_time:                        0.
% 3.68/0.98  monotx_time:                            0.001
% 3.68/0.98  subtype_inf_time:                       0.
% 3.68/0.98  
% 3.68/0.98  ------ Problem properties
% 3.68/0.98  
% 3.68/0.98  clauses:                                19
% 3.68/0.98  conjectures:                            4
% 3.68/0.98  epr:                                    0
% 3.68/0.98  horn:                                   16
% 3.68/0.98  ground:                                 4
% 3.68/0.98  unary:                                  6
% 3.68/0.98  binary:                                 0
% 3.68/0.98  lits:                                   85
% 3.68/0.98  lits_eq:                                10
% 3.68/0.98  fd_pure:                                0
% 3.68/0.98  fd_pseudo:                              0
% 3.68/0.98  fd_cond:                                0
% 3.68/0.98  fd_pseudo_cond:                         4
% 3.68/0.98  ac_symbols:                             0
% 3.68/0.98  
% 3.68/0.98  ------ Propositional Solver
% 3.68/0.98  
% 3.68/0.98  prop_solver_calls:                      32
% 3.68/0.98  prop_fast_solver_calls:                 1932
% 3.68/0.98  smt_solver_calls:                       0
% 3.68/0.98  smt_fast_solver_calls:                  0
% 3.68/0.98  prop_num_of_clauses:                    2918
% 3.68/0.98  prop_preprocess_simplified:             7595
% 3.68/0.98  prop_fo_subsumed:                       42
% 3.68/0.98  prop_solver_time:                       0.
% 3.68/0.98  smt_solver_time:                        0.
% 3.68/0.98  smt_fast_solver_time:                   0.
% 3.68/0.98  prop_fast_solver_time:                  0.
% 3.68/0.98  prop_unsat_core_time:                   0.
% 3.68/0.98  
% 3.68/0.98  ------ QBF
% 3.68/0.98  
% 3.68/0.98  qbf_q_res:                              0
% 3.68/0.98  qbf_num_tautologies:                    0
% 3.68/0.98  qbf_prep_cycles:                        0
% 3.68/0.98  
% 3.68/0.98  ------ BMC1
% 3.68/0.98  
% 3.68/0.98  bmc1_current_bound:                     -1
% 3.68/0.98  bmc1_last_solved_bound:                 -1
% 3.68/0.98  bmc1_unsat_core_size:                   -1
% 3.68/0.98  bmc1_unsat_core_parents_size:           -1
% 3.68/0.98  bmc1_merge_next_fun:                    0
% 3.68/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.68/0.98  
% 3.68/0.98  ------ Instantiation
% 3.68/0.98  
% 3.68/0.98  inst_num_of_clauses:                    645
% 3.68/0.98  inst_num_in_passive:                    133
% 3.68/0.98  inst_num_in_active:                     464
% 3.68/0.98  inst_num_in_unprocessed:                48
% 3.68/0.98  inst_num_of_loops:                      490
% 3.68/0.98  inst_num_of_learning_restarts:          0
% 3.68/0.98  inst_num_moves_active_passive:          25
% 3.68/0.98  inst_lit_activity:                      0
% 3.68/0.98  inst_lit_activity_moves:                1
% 3.68/0.98  inst_num_tautologies:                   0
% 3.68/0.98  inst_num_prop_implied:                  0
% 3.68/0.98  inst_num_existing_simplified:           0
% 3.68/0.98  inst_num_eq_res_simplified:             0
% 3.68/0.98  inst_num_child_elim:                    0
% 3.68/0.98  inst_num_of_dismatching_blockings:      166
% 3.68/0.98  inst_num_of_non_proper_insts:           315
% 3.68/0.98  inst_num_of_duplicates:                 0
% 3.68/0.98  inst_inst_num_from_inst_to_res:         0
% 3.68/0.98  inst_dismatching_checking_time:         0.
% 3.68/0.98  
% 3.68/0.98  ------ Resolution
% 3.68/0.98  
% 3.68/0.98  res_num_of_clauses:                     0
% 3.68/0.98  res_num_in_passive:                     0
% 3.68/0.98  res_num_in_active:                      0
% 3.68/0.98  res_num_of_loops:                       139
% 3.68/0.98  res_forward_subset_subsumed:            10
% 3.68/0.98  res_backward_subset_subsumed:           0
% 3.68/0.98  res_forward_subsumed:                   0
% 3.68/0.98  res_backward_subsumed:                  0
% 3.68/0.98  res_forward_subsumption_resolution:     3
% 3.68/0.98  res_backward_subsumption_resolution:    0
% 3.68/0.98  res_clause_to_clause_subsumption:       1305
% 3.68/0.98  res_orphan_elimination:                 0
% 3.68/0.98  res_tautology_del:                      13
% 3.68/0.98  res_num_eq_res_simplified:              0
% 3.68/0.98  res_num_sel_changes:                    0
% 3.68/0.98  res_moves_from_active_to_pass:          0
% 3.68/0.98  
% 3.68/0.98  ------ Superposition
% 3.68/0.98  
% 3.68/0.98  sup_time_total:                         0.
% 3.68/0.98  sup_time_generating:                    0.
% 3.68/0.98  sup_time_sim_full:                      0.
% 3.68/0.98  sup_time_sim_immed:                     0.
% 3.68/0.98  
% 3.68/0.98  sup_num_of_clauses:                     234
% 3.68/0.98  sup_num_in_active:                      84
% 3.68/0.98  sup_num_in_passive:                     150
% 3.68/0.98  sup_num_of_loops:                       97
% 3.68/0.98  sup_fw_superposition:                   182
% 3.68/0.98  sup_bw_superposition:                   102
% 3.68/0.98  sup_immediate_simplified:               141
% 3.68/0.98  sup_given_eliminated:                   0
% 3.68/0.98  comparisons_done:                       0
% 3.68/0.98  comparisons_avoided:                    0
% 3.68/0.98  
% 3.68/0.98  ------ Simplifications
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  sim_fw_subset_subsumed:                 0
% 3.68/0.98  sim_bw_subset_subsumed:                 1
% 3.68/0.98  sim_fw_subsumed:                        7
% 3.68/0.98  sim_bw_subsumed:                        0
% 3.68/0.98  sim_fw_subsumption_res:                 0
% 3.68/0.98  sim_bw_subsumption_res:                 0
% 3.68/0.98  sim_tautology_del:                      1
% 3.68/0.98  sim_eq_tautology_del:                   2
% 3.68/0.98  sim_eq_res_simp:                        0
% 3.68/0.98  sim_fw_demodulated:                     7
% 3.68/0.98  sim_bw_demodulated:                     14
% 3.68/0.98  sim_light_normalised:                   145
% 3.68/0.98  sim_joinable_taut:                      0
% 3.68/0.98  sim_joinable_simp:                      0
% 3.68/0.98  sim_ac_normalised:                      0
% 3.68/0.98  sim_smt_subsumption:                    0
% 3.68/0.98  
%------------------------------------------------------------------------------
