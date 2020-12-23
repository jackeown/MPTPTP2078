%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:20:11 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 321 expanded)
%              Number of clauses        :   70 ( 107 expanded)
%              Number of leaves         :   15 (  73 expanded)
%              Depth                    :   17
%              Number of atoms          :  611 (1468 expanded)
%              Number of equality atoms :   60 (  83 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v2_lattice3(k2_yellow_1(X0))
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
               => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( v2_lattice3(k2_yellow_1(X0))
         => ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
          & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
     => ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,sK3),k3_xboole_0(X1,sK3))
        & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
     => ( ? [X2] :
            ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),sK2,X2),k3_xboole_0(sK2,X2))
            & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
        & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
                & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
            & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
        & v2_lattice3(k2_yellow_1(X0))
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK1),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK1))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1))) )
      & v2_lattice3(k2_yellow_1(sK1))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k3_xboole_0(sK2,sK3))
    & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
    & v2_lattice3(k2_yellow_1(sK1))
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f43,f42,f41])).

fof(f66,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,(
    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f69,plain,(
    m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f58,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f15,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f60,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f67,plain,(
    v2_lattice3(k2_yellow_1(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f70,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k3_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f44])).

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

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k12_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k12_lattice3(X0,X1,X2) = X3
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
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k12_lattice3(X0,X1,X2) = X3
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
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k12_lattice3(X0,X1,X2) = X3
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
                      | k12_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k12_lattice3(X0,X1,X2) = X3
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
                      | k12_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f35])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k12_lattice3(X0,X1,X2) = X3
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
                      | k12_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK0(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK0(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK0(X0,X1,X2,X3),X1)
        & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k12_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,sK0(X0,X1,X2,X3),X3)
                        & r1_orders_2(X0,sK0(X0,X1,X2,X3),X2)
                        & r1_orders_2(X0,sK0(X0,X1,X2,X3),X1)
                        & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k12_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X1)
      | k12_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X1)
      | ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X2)
      | k12_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ~ v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_20,plain,
    ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | r1_tarski(X1,X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_25,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_273,plain,
    ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | r1_tarski(X1,X2)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_25])).

cnf(c_274,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK1),X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
    | r1_tarski(X0,X1) ),
    inference(unflattening,[status(thm)],[c_273])).

cnf(c_2798,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),sK2,sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | r1_tarski(k12_lattice3(k2_yellow_1(sK1),sK2,sK3),X0) ),
    inference(instantiation,[status(thm)],[c_274])).

cnf(c_8079,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2)
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
    | r1_tarski(k12_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_2798])).

cnf(c_8076,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3)
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    | r1_tarski(k12_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_2798])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2110,plain,
    ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_18,plain,
    ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2122,plain,
    ( m1_subset_1(sK2,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2110,c_18])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2111,plain,
    ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2125,plain,
    ( m1_subset_1(sK3,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2111,c_18])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_13,plain,
    ( l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_771,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0)
    | k2_yellow_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_13])).

cnf(c_772,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | ~ v5_orders_2(k2_yellow_1(X1))
    | ~ v2_lattice3(k2_yellow_1(X1))
    | k11_lattice3(k2_yellow_1(X1),X0,X2) = k12_lattice3(k2_yellow_1(X1),X0,X2) ),
    inference(unflattening,[status(thm)],[c_771])).

cnf(c_14,plain,
    ( v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_786,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | ~ v2_lattice3(k2_yellow_1(X1))
    | k11_lattice3(k2_yellow_1(X1),X0,X2) = k12_lattice3(k2_yellow_1(X1),X0,X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_772,c_14])).

cnf(c_2097,plain,
    ( k11_lattice3(k2_yellow_1(X0),X1,X2) = k12_lattice3(k2_yellow_1(X0),X1,X2)
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | v2_lattice3(k2_yellow_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_786])).

cnf(c_2181,plain,
    ( k11_lattice3(k2_yellow_1(X0),X1,X2) = k12_lattice3(k2_yellow_1(X0),X1,X2)
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | v2_lattice3(k2_yellow_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2097,c_18])).

cnf(c_3425,plain,
    ( k11_lattice3(k2_yellow_1(sK1),X0,sK3) = k12_lattice3(k2_yellow_1(sK1),X0,sK3)
    | m1_subset_1(X0,sK1) != iProver_top
    | v2_lattice3(k2_yellow_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2125,c_2181])).

cnf(c_24,negated_conjecture,
    ( v2_lattice3(k2_yellow_1(sK1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_27,plain,
    ( v2_lattice3(k2_yellow_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4494,plain,
    ( m1_subset_1(X0,sK1) != iProver_top
    | k11_lattice3(k2_yellow_1(sK1),X0,sK3) = k12_lattice3(k2_yellow_1(sK1),X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3425,c_27])).

cnf(c_4495,plain,
    ( k11_lattice3(k2_yellow_1(sK1),X0,sK3) = k12_lattice3(k2_yellow_1(sK1),X0,sK3)
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4494])).

cnf(c_4502,plain,
    ( k11_lattice3(k2_yellow_1(sK1),sK2,sK3) = k12_lattice3(k2_yellow_1(sK1),sK2,sK3) ),
    inference(superposition,[status(thm)],[c_2122,c_4495])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2113,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k3_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k3_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2112,plain,
    ( r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k3_xboole_0(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3043,plain,
    ( r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3) != iProver_top
    | r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2113,c_2112])).

cnf(c_4521,plain,
    ( r1_tarski(k12_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3) != iProver_top
    | r1_tarski(k12_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4502,c_3043])).

cnf(c_4529,plain,
    ( ~ r1_tarski(k12_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3)
    | ~ r1_tarski(k12_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4521])).

cnf(c_1,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_15,plain,
    ( v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_355,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_15])).

cnf(c_356,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | v2_struct_0(k2_yellow_1(X0))
    | ~ l1_orders_2(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_355])).

cnf(c_360,plain,
    ( v2_struct_0(k2_yellow_1(X0))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r1_orders_2(k2_yellow_1(X0),X1,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_356,c_13])).

cnf(c_361,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | v2_struct_0(k2_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_360])).

cnf(c_2464,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK1),X0,sK2)
    | r3_orders_2(k2_yellow_1(sK1),X0,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
    | v2_struct_0(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_361])).

cnf(c_3982,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2)
    | r3_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2)
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
    | v2_struct_0(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_2464])).

cnf(c_2459,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK1),X0,sK3)
    | r3_orders_2(k2_yellow_1(sK1),X0,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    | v2_struct_0(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_361])).

cnf(c_3119,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3)
    | r3_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3)
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    | v2_struct_0(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_2459])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k12_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_794,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k12_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | k2_yellow_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_13])).

cnf(c_795,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | m1_subset_1(k12_lattice3(k2_yellow_1(X1),X0,X2),u1_struct_0(k2_yellow_1(X1)))
    | ~ v5_orders_2(k2_yellow_1(X1))
    | ~ v2_lattice3(k2_yellow_1(X1)) ),
    inference(unflattening,[status(thm)],[c_794])).

cnf(c_809,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | m1_subset_1(k12_lattice3(k2_yellow_1(X1),X0,X2),u1_struct_0(k2_yellow_1(X1)))
    | ~ v2_lattice3(k2_yellow_1(X1)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_795,c_14])).

cnf(c_12,plain,
    ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_522,plain,
    ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_13])).

cnf(c_523,plain,
    ( r1_orders_2(k2_yellow_1(X0),k12_lattice3(k2_yellow_1(X0),X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
    | ~ v5_orders_2(k2_yellow_1(X0))
    | ~ v2_lattice3(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_522])).

cnf(c_527,plain,
    ( ~ m1_subset_1(k12_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | r1_orders_2(k2_yellow_1(X0),k12_lattice3(k2_yellow_1(X0),X1,X2),X1)
    | ~ v2_lattice3(k2_yellow_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_523,c_14])).

cnf(c_528,plain,
    ( r1_orders_2(k2_yellow_1(X0),k12_lattice3(k2_yellow_1(X0),X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
    | ~ v2_lattice3(k2_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_527])).

cnf(c_814,plain,
    ( r1_orders_2(k2_yellow_1(X0),k12_lattice3(k2_yellow_1(X0),X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ v2_lattice3(k2_yellow_1(X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_809,c_528])).

cnf(c_2435,plain,
    ( r1_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),X0,sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    | ~ v2_lattice3(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_814])).

cnf(c_3075,plain,
    ( r1_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
    | ~ v2_lattice3(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_2435])).

cnf(c_11,plain,
    ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_549,plain,
    ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_13])).

cnf(c_550,plain,
    ( r1_orders_2(k2_yellow_1(X0),k12_lattice3(k2_yellow_1(X0),X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
    | ~ v5_orders_2(k2_yellow_1(X0))
    | ~ v2_lattice3(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_549])).

cnf(c_552,plain,
    ( ~ m1_subset_1(k12_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | r1_orders_2(k2_yellow_1(X0),k12_lattice3(k2_yellow_1(X0),X1,X2),X2)
    | ~ v2_lattice3(k2_yellow_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_550,c_14])).

cnf(c_553,plain,
    ( r1_orders_2(k2_yellow_1(X0),k12_lattice3(k2_yellow_1(X0),X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
    | ~ v2_lattice3(k2_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_552])).

cnf(c_813,plain,
    ( r1_orders_2(k2_yellow_1(X0),k12_lattice3(k2_yellow_1(X0),X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ v2_lattice3(k2_yellow_1(X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_809,c_553])).

cnf(c_2425,plain,
    ( r1_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),X0,sK3),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    | ~ v2_lattice3(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_813])).

cnf(c_2910,plain,
    ( r1_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
    | ~ v2_lattice3(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_2425])).

cnf(c_2420,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | m1_subset_1(k12_lattice3(k2_yellow_1(sK1),sK2,X0),u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
    | ~ v2_lattice3(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_809])).

cnf(c_2571,plain,
    ( m1_subset_1(k12_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
    | ~ v2_lattice3(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_2420])).

cnf(c_16,plain,
    ( v1_xboole_0(X0)
    | ~ v2_struct_0(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_40,plain,
    ( v1_xboole_0(sK1)
    | ~ v2_struct_0(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8079,c_8076,c_4529,c_3982,c_3119,c_3075,c_2910,c_2571,c_40,c_22,c_23,c_24,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : iproveropt_run.sh %d %s
% 0.10/0.31  % Computer   : n023.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % WCLimit    : 600
% 0.10/0.31  % DateTime   : Tue Dec  1 16:28:50 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.10/0.32  % Running in FOF mode
% 3.24/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/0.97  
% 3.24/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.24/0.97  
% 3.24/0.97  ------  iProver source info
% 3.24/0.97  
% 3.24/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.24/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.24/0.97  git: non_committed_changes: false
% 3.24/0.97  git: last_make_outside_of_git: false
% 3.24/0.97  
% 3.24/0.97  ------ 
% 3.24/0.97  
% 3.24/0.97  ------ Input Options
% 3.24/0.97  
% 3.24/0.97  --out_options                           all
% 3.24/0.97  --tptp_safe_out                         true
% 3.24/0.97  --problem_path                          ""
% 3.24/0.97  --include_path                          ""
% 3.24/0.97  --clausifier                            res/vclausify_rel
% 3.24/0.97  --clausifier_options                    --mode clausify
% 3.24/0.97  --stdin                                 false
% 3.24/0.97  --stats_out                             all
% 3.24/0.97  
% 3.24/0.97  ------ General Options
% 3.24/0.97  
% 3.24/0.97  --fof                                   false
% 3.24/0.97  --time_out_real                         305.
% 3.24/0.97  --time_out_virtual                      -1.
% 3.24/0.97  --symbol_type_check                     false
% 3.24/0.97  --clausify_out                          false
% 3.24/0.97  --sig_cnt_out                           false
% 3.24/0.97  --trig_cnt_out                          false
% 3.24/0.97  --trig_cnt_out_tolerance                1.
% 3.24/0.97  --trig_cnt_out_sk_spl                   false
% 3.24/0.97  --abstr_cl_out                          false
% 3.24/0.97  
% 3.24/0.97  ------ Global Options
% 3.24/0.97  
% 3.24/0.97  --schedule                              default
% 3.24/0.97  --add_important_lit                     false
% 3.24/0.97  --prop_solver_per_cl                    1000
% 3.24/0.97  --min_unsat_core                        false
% 3.24/0.97  --soft_assumptions                      false
% 3.24/0.97  --soft_lemma_size                       3
% 3.24/0.97  --prop_impl_unit_size                   0
% 3.24/0.97  --prop_impl_unit                        []
% 3.24/0.97  --share_sel_clauses                     true
% 3.24/0.97  --reset_solvers                         false
% 3.24/0.97  --bc_imp_inh                            [conj_cone]
% 3.24/0.97  --conj_cone_tolerance                   3.
% 3.24/0.97  --extra_neg_conj                        none
% 3.24/0.97  --large_theory_mode                     true
% 3.24/0.97  --prolific_symb_bound                   200
% 3.24/0.97  --lt_threshold                          2000
% 3.24/0.97  --clause_weak_htbl                      true
% 3.24/0.97  --gc_record_bc_elim                     false
% 3.24/0.97  
% 3.24/0.97  ------ Preprocessing Options
% 3.24/0.97  
% 3.24/0.97  --preprocessing_flag                    true
% 3.24/0.97  --time_out_prep_mult                    0.1
% 3.24/0.97  --splitting_mode                        input
% 3.24/0.97  --splitting_grd                         true
% 3.24/0.97  --splitting_cvd                         false
% 3.24/0.97  --splitting_cvd_svl                     false
% 3.24/0.97  --splitting_nvd                         32
% 3.24/0.97  --sub_typing                            true
% 3.24/0.97  --prep_gs_sim                           true
% 3.24/0.97  --prep_unflatten                        true
% 3.24/0.97  --prep_res_sim                          true
% 3.24/0.97  --prep_upred                            true
% 3.24/0.97  --prep_sem_filter                       exhaustive
% 3.24/0.97  --prep_sem_filter_out                   false
% 3.24/0.97  --pred_elim                             true
% 3.24/0.97  --res_sim_input                         true
% 3.24/0.97  --eq_ax_congr_red                       true
% 3.24/0.97  --pure_diseq_elim                       true
% 3.24/0.97  --brand_transform                       false
% 3.24/0.97  --non_eq_to_eq                          false
% 3.24/0.97  --prep_def_merge                        true
% 3.24/0.97  --prep_def_merge_prop_impl              false
% 3.24/0.97  --prep_def_merge_mbd                    true
% 3.24/0.97  --prep_def_merge_tr_red                 false
% 3.24/0.97  --prep_def_merge_tr_cl                  false
% 3.24/0.97  --smt_preprocessing                     true
% 3.24/0.97  --smt_ac_axioms                         fast
% 3.24/0.97  --preprocessed_out                      false
% 3.24/0.97  --preprocessed_stats                    false
% 3.24/0.97  
% 3.24/0.97  ------ Abstraction refinement Options
% 3.24/0.97  
% 3.24/0.97  --abstr_ref                             []
% 3.24/0.97  --abstr_ref_prep                        false
% 3.24/0.97  --abstr_ref_until_sat                   false
% 3.24/0.97  --abstr_ref_sig_restrict                funpre
% 3.24/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.24/0.97  --abstr_ref_under                       []
% 3.24/0.97  
% 3.24/0.97  ------ SAT Options
% 3.24/0.97  
% 3.24/0.97  --sat_mode                              false
% 3.24/0.97  --sat_fm_restart_options                ""
% 3.24/0.97  --sat_gr_def                            false
% 3.24/0.97  --sat_epr_types                         true
% 3.24/0.97  --sat_non_cyclic_types                  false
% 3.24/0.97  --sat_finite_models                     false
% 3.24/0.97  --sat_fm_lemmas                         false
% 3.24/0.97  --sat_fm_prep                           false
% 3.24/0.97  --sat_fm_uc_incr                        true
% 3.24/0.97  --sat_out_model                         small
% 3.24/0.97  --sat_out_clauses                       false
% 3.24/0.97  
% 3.24/0.97  ------ QBF Options
% 3.24/0.97  
% 3.24/0.97  --qbf_mode                              false
% 3.24/0.97  --qbf_elim_univ                         false
% 3.24/0.97  --qbf_dom_inst                          none
% 3.24/0.97  --qbf_dom_pre_inst                      false
% 3.24/0.97  --qbf_sk_in                             false
% 3.24/0.97  --qbf_pred_elim                         true
% 3.24/0.97  --qbf_split                             512
% 3.24/0.97  
% 3.24/0.97  ------ BMC1 Options
% 3.24/0.97  
% 3.24/0.97  --bmc1_incremental                      false
% 3.24/0.97  --bmc1_axioms                           reachable_all
% 3.24/0.97  --bmc1_min_bound                        0
% 3.24/0.97  --bmc1_max_bound                        -1
% 3.24/0.97  --bmc1_max_bound_default                -1
% 3.24/0.97  --bmc1_symbol_reachability              true
% 3.24/0.97  --bmc1_property_lemmas                  false
% 3.24/0.97  --bmc1_k_induction                      false
% 3.24/0.97  --bmc1_non_equiv_states                 false
% 3.24/0.97  --bmc1_deadlock                         false
% 3.24/0.97  --bmc1_ucm                              false
% 3.24/0.97  --bmc1_add_unsat_core                   none
% 3.24/0.97  --bmc1_unsat_core_children              false
% 3.24/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.24/0.97  --bmc1_out_stat                         full
% 3.24/0.97  --bmc1_ground_init                      false
% 3.24/0.97  --bmc1_pre_inst_next_state              false
% 3.24/0.97  --bmc1_pre_inst_state                   false
% 3.24/0.97  --bmc1_pre_inst_reach_state             false
% 3.24/0.97  --bmc1_out_unsat_core                   false
% 3.24/0.97  --bmc1_aig_witness_out                  false
% 3.24/0.97  --bmc1_verbose                          false
% 3.24/0.97  --bmc1_dump_clauses_tptp                false
% 3.24/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.24/0.97  --bmc1_dump_file                        -
% 3.24/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.24/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.24/0.97  --bmc1_ucm_extend_mode                  1
% 3.24/0.97  --bmc1_ucm_init_mode                    2
% 3.24/0.97  --bmc1_ucm_cone_mode                    none
% 3.24/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.24/0.97  --bmc1_ucm_relax_model                  4
% 3.24/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.24/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.24/0.97  --bmc1_ucm_layered_model                none
% 3.24/0.97  --bmc1_ucm_max_lemma_size               10
% 3.24/0.97  
% 3.24/0.97  ------ AIG Options
% 3.24/0.97  
% 3.24/0.97  --aig_mode                              false
% 3.24/0.97  
% 3.24/0.97  ------ Instantiation Options
% 3.24/0.97  
% 3.24/0.97  --instantiation_flag                    true
% 3.24/0.97  --inst_sos_flag                         false
% 3.24/0.97  --inst_sos_phase                        true
% 3.24/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.24/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.24/0.97  --inst_lit_sel_side                     num_symb
% 3.24/0.97  --inst_solver_per_active                1400
% 3.24/0.97  --inst_solver_calls_frac                1.
% 3.24/0.97  --inst_passive_queue_type               priority_queues
% 3.24/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.24/0.97  --inst_passive_queues_freq              [25;2]
% 3.24/0.97  --inst_dismatching                      true
% 3.24/0.97  --inst_eager_unprocessed_to_passive     true
% 3.24/0.97  --inst_prop_sim_given                   true
% 3.24/0.97  --inst_prop_sim_new                     false
% 3.24/0.97  --inst_subs_new                         false
% 3.24/0.97  --inst_eq_res_simp                      false
% 3.24/0.97  --inst_subs_given                       false
% 3.24/0.97  --inst_orphan_elimination               true
% 3.24/0.97  --inst_learning_loop_flag               true
% 3.24/0.97  --inst_learning_start                   3000
% 3.24/0.97  --inst_learning_factor                  2
% 3.24/0.97  --inst_start_prop_sim_after_learn       3
% 3.24/0.97  --inst_sel_renew                        solver
% 3.24/0.97  --inst_lit_activity_flag                true
% 3.24/0.97  --inst_restr_to_given                   false
% 3.24/0.97  --inst_activity_threshold               500
% 3.24/0.97  --inst_out_proof                        true
% 3.24/0.97  
% 3.24/0.97  ------ Resolution Options
% 3.24/0.97  
% 3.24/0.97  --resolution_flag                       true
% 3.24/0.97  --res_lit_sel                           adaptive
% 3.24/0.97  --res_lit_sel_side                      none
% 3.24/0.97  --res_ordering                          kbo
% 3.24/0.97  --res_to_prop_solver                    active
% 3.24/0.97  --res_prop_simpl_new                    false
% 3.24/0.97  --res_prop_simpl_given                  true
% 3.24/0.97  --res_passive_queue_type                priority_queues
% 3.24/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.24/0.97  --res_passive_queues_freq               [15;5]
% 3.24/0.97  --res_forward_subs                      full
% 3.24/0.97  --res_backward_subs                     full
% 3.24/0.97  --res_forward_subs_resolution           true
% 3.24/0.97  --res_backward_subs_resolution          true
% 3.24/0.97  --res_orphan_elimination                true
% 3.24/0.97  --res_time_limit                        2.
% 3.24/0.97  --res_out_proof                         true
% 3.24/0.97  
% 3.24/0.97  ------ Superposition Options
% 3.24/0.97  
% 3.24/0.97  --superposition_flag                    true
% 3.24/0.97  --sup_passive_queue_type                priority_queues
% 3.24/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.24/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.24/0.97  --demod_completeness_check              fast
% 3.24/0.97  --demod_use_ground                      true
% 3.24/0.97  --sup_to_prop_solver                    passive
% 3.24/0.97  --sup_prop_simpl_new                    true
% 3.24/0.97  --sup_prop_simpl_given                  true
% 3.24/0.97  --sup_fun_splitting                     false
% 3.24/0.97  --sup_smt_interval                      50000
% 3.24/0.97  
% 3.24/0.97  ------ Superposition Simplification Setup
% 3.24/0.97  
% 3.24/0.97  --sup_indices_passive                   []
% 3.24/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.24/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/0.97  --sup_full_bw                           [BwDemod]
% 3.24/0.97  --sup_immed_triv                        [TrivRules]
% 3.24/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.24/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/0.97  --sup_immed_bw_main                     []
% 3.24/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.24/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/0.97  
% 3.24/0.97  ------ Combination Options
% 3.24/0.97  
% 3.24/0.97  --comb_res_mult                         3
% 3.24/0.97  --comb_sup_mult                         2
% 3.24/0.97  --comb_inst_mult                        10
% 3.24/0.97  
% 3.24/0.97  ------ Debug Options
% 3.24/0.97  
% 3.24/0.97  --dbg_backtrace                         false
% 3.24/0.97  --dbg_dump_prop_clauses                 false
% 3.24/0.97  --dbg_dump_prop_clauses_file            -
% 3.24/0.97  --dbg_out_stat                          false
% 3.24/0.97  ------ Parsing...
% 3.24/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.24/0.97  
% 3.24/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.24/0.97  
% 3.24/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.24/0.97  
% 3.24/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.24/0.97  ------ Proving...
% 3.24/0.97  ------ Problem Properties 
% 3.24/0.97  
% 3.24/0.97  
% 3.24/0.97  clauses                                 22
% 3.24/0.97  conjectures                             4
% 3.24/0.97  EPR                                     0
% 3.24/0.97  Horn                                    17
% 3.24/0.97  unary                                   7
% 3.24/0.97  binary                                  0
% 3.24/0.97  lits                                    88
% 3.24/0.97  lits eq                                 8
% 3.24/0.97  fd_pure                                 0
% 3.24/0.97  fd_pseudo                               0
% 3.24/0.97  fd_cond                                 0
% 3.24/0.97  fd_pseudo_cond                          4
% 3.24/0.97  AC symbols                              0
% 3.24/0.97  
% 3.24/0.97  ------ Schedule dynamic 5 is on 
% 3.24/0.97  
% 3.24/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.24/0.97  
% 3.24/0.97  
% 3.24/0.97  ------ 
% 3.24/0.97  Current options:
% 3.24/0.97  ------ 
% 3.24/0.97  
% 3.24/0.97  ------ Input Options
% 3.24/0.97  
% 3.24/0.97  --out_options                           all
% 3.24/0.97  --tptp_safe_out                         true
% 3.24/0.97  --problem_path                          ""
% 3.24/0.97  --include_path                          ""
% 3.24/0.97  --clausifier                            res/vclausify_rel
% 3.24/0.97  --clausifier_options                    --mode clausify
% 3.24/0.97  --stdin                                 false
% 3.24/0.97  --stats_out                             all
% 3.24/0.97  
% 3.24/0.97  ------ General Options
% 3.24/0.97  
% 3.24/0.97  --fof                                   false
% 3.24/0.97  --time_out_real                         305.
% 3.24/0.97  --time_out_virtual                      -1.
% 3.24/0.97  --symbol_type_check                     false
% 3.24/0.97  --clausify_out                          false
% 3.24/0.97  --sig_cnt_out                           false
% 3.24/0.97  --trig_cnt_out                          false
% 3.24/0.97  --trig_cnt_out_tolerance                1.
% 3.24/0.97  --trig_cnt_out_sk_spl                   false
% 3.24/0.97  --abstr_cl_out                          false
% 3.24/0.97  
% 3.24/0.97  ------ Global Options
% 3.24/0.97  
% 3.24/0.97  --schedule                              default
% 3.24/0.97  --add_important_lit                     false
% 3.24/0.97  --prop_solver_per_cl                    1000
% 3.24/0.97  --min_unsat_core                        false
% 3.24/0.97  --soft_assumptions                      false
% 3.24/0.97  --soft_lemma_size                       3
% 3.24/0.97  --prop_impl_unit_size                   0
% 3.24/0.97  --prop_impl_unit                        []
% 3.24/0.97  --share_sel_clauses                     true
% 3.24/0.97  --reset_solvers                         false
% 3.24/0.97  --bc_imp_inh                            [conj_cone]
% 3.24/0.97  --conj_cone_tolerance                   3.
% 3.24/0.97  --extra_neg_conj                        none
% 3.24/0.97  --large_theory_mode                     true
% 3.24/0.97  --prolific_symb_bound                   200
% 3.24/0.97  --lt_threshold                          2000
% 3.24/0.97  --clause_weak_htbl                      true
% 3.24/0.97  --gc_record_bc_elim                     false
% 3.24/0.97  
% 3.24/0.97  ------ Preprocessing Options
% 3.24/0.97  
% 3.24/0.97  --preprocessing_flag                    true
% 3.24/0.97  --time_out_prep_mult                    0.1
% 3.24/0.97  --splitting_mode                        input
% 3.24/0.97  --splitting_grd                         true
% 3.24/0.97  --splitting_cvd                         false
% 3.24/0.97  --splitting_cvd_svl                     false
% 3.24/0.97  --splitting_nvd                         32
% 3.24/0.97  --sub_typing                            true
% 3.24/0.97  --prep_gs_sim                           true
% 3.24/0.97  --prep_unflatten                        true
% 3.24/0.97  --prep_res_sim                          true
% 3.24/0.97  --prep_upred                            true
% 3.24/0.97  --prep_sem_filter                       exhaustive
% 3.24/0.97  --prep_sem_filter_out                   false
% 3.24/0.97  --pred_elim                             true
% 3.24/0.97  --res_sim_input                         true
% 3.24/0.97  --eq_ax_congr_red                       true
% 3.24/0.97  --pure_diseq_elim                       true
% 3.24/0.97  --brand_transform                       false
% 3.24/0.97  --non_eq_to_eq                          false
% 3.24/0.97  --prep_def_merge                        true
% 3.24/0.97  --prep_def_merge_prop_impl              false
% 3.24/0.97  --prep_def_merge_mbd                    true
% 3.24/0.97  --prep_def_merge_tr_red                 false
% 3.24/0.97  --prep_def_merge_tr_cl                  false
% 3.24/0.97  --smt_preprocessing                     true
% 3.24/0.97  --smt_ac_axioms                         fast
% 3.24/0.97  --preprocessed_out                      false
% 3.24/0.97  --preprocessed_stats                    false
% 3.24/0.97  
% 3.24/0.97  ------ Abstraction refinement Options
% 3.24/0.97  
% 3.24/0.97  --abstr_ref                             []
% 3.24/0.97  --abstr_ref_prep                        false
% 3.24/0.97  --abstr_ref_until_sat                   false
% 3.24/0.97  --abstr_ref_sig_restrict                funpre
% 3.24/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.24/0.97  --abstr_ref_under                       []
% 3.24/0.97  
% 3.24/0.97  ------ SAT Options
% 3.24/0.97  
% 3.24/0.97  --sat_mode                              false
% 3.24/0.97  --sat_fm_restart_options                ""
% 3.24/0.97  --sat_gr_def                            false
% 3.24/0.97  --sat_epr_types                         true
% 3.24/0.97  --sat_non_cyclic_types                  false
% 3.24/0.97  --sat_finite_models                     false
% 3.24/0.97  --sat_fm_lemmas                         false
% 3.24/0.97  --sat_fm_prep                           false
% 3.24/0.97  --sat_fm_uc_incr                        true
% 3.24/0.97  --sat_out_model                         small
% 3.24/0.97  --sat_out_clauses                       false
% 3.24/0.97  
% 3.24/0.97  ------ QBF Options
% 3.24/0.97  
% 3.24/0.97  --qbf_mode                              false
% 3.24/0.97  --qbf_elim_univ                         false
% 3.24/0.97  --qbf_dom_inst                          none
% 3.24/0.97  --qbf_dom_pre_inst                      false
% 3.24/0.97  --qbf_sk_in                             false
% 3.24/0.97  --qbf_pred_elim                         true
% 3.24/0.97  --qbf_split                             512
% 3.24/0.97  
% 3.24/0.97  ------ BMC1 Options
% 3.24/0.97  
% 3.24/0.97  --bmc1_incremental                      false
% 3.24/0.97  --bmc1_axioms                           reachable_all
% 3.24/0.97  --bmc1_min_bound                        0
% 3.24/0.97  --bmc1_max_bound                        -1
% 3.24/0.97  --bmc1_max_bound_default                -1
% 3.24/0.97  --bmc1_symbol_reachability              true
% 3.24/0.97  --bmc1_property_lemmas                  false
% 3.24/0.97  --bmc1_k_induction                      false
% 3.24/0.97  --bmc1_non_equiv_states                 false
% 3.24/0.97  --bmc1_deadlock                         false
% 3.24/0.97  --bmc1_ucm                              false
% 3.24/0.97  --bmc1_add_unsat_core                   none
% 3.24/0.97  --bmc1_unsat_core_children              false
% 3.24/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.24/0.97  --bmc1_out_stat                         full
% 3.24/0.97  --bmc1_ground_init                      false
% 3.24/0.97  --bmc1_pre_inst_next_state              false
% 3.24/0.97  --bmc1_pre_inst_state                   false
% 3.24/0.97  --bmc1_pre_inst_reach_state             false
% 3.24/0.97  --bmc1_out_unsat_core                   false
% 3.24/0.97  --bmc1_aig_witness_out                  false
% 3.24/0.97  --bmc1_verbose                          false
% 3.24/0.97  --bmc1_dump_clauses_tptp                false
% 3.24/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.24/0.97  --bmc1_dump_file                        -
% 3.24/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.24/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.24/0.97  --bmc1_ucm_extend_mode                  1
% 3.24/0.97  --bmc1_ucm_init_mode                    2
% 3.24/0.97  --bmc1_ucm_cone_mode                    none
% 3.24/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.24/0.97  --bmc1_ucm_relax_model                  4
% 3.24/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.24/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.24/0.97  --bmc1_ucm_layered_model                none
% 3.24/0.97  --bmc1_ucm_max_lemma_size               10
% 3.24/0.97  
% 3.24/0.97  ------ AIG Options
% 3.24/0.97  
% 3.24/0.97  --aig_mode                              false
% 3.24/0.97  
% 3.24/0.97  ------ Instantiation Options
% 3.24/0.97  
% 3.24/0.97  --instantiation_flag                    true
% 3.24/0.97  --inst_sos_flag                         false
% 3.24/0.97  --inst_sos_phase                        true
% 3.24/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.24/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.24/0.97  --inst_lit_sel_side                     none
% 3.24/0.97  --inst_solver_per_active                1400
% 3.24/0.97  --inst_solver_calls_frac                1.
% 3.24/0.97  --inst_passive_queue_type               priority_queues
% 3.24/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.24/0.97  --inst_passive_queues_freq              [25;2]
% 3.24/0.97  --inst_dismatching                      true
% 3.24/0.97  --inst_eager_unprocessed_to_passive     true
% 3.24/0.97  --inst_prop_sim_given                   true
% 3.24/0.97  --inst_prop_sim_new                     false
% 3.24/0.97  --inst_subs_new                         false
% 3.24/0.97  --inst_eq_res_simp                      false
% 3.24/0.97  --inst_subs_given                       false
% 3.24/0.97  --inst_orphan_elimination               true
% 3.24/0.97  --inst_learning_loop_flag               true
% 3.24/0.97  --inst_learning_start                   3000
% 3.24/0.97  --inst_learning_factor                  2
% 3.24/0.97  --inst_start_prop_sim_after_learn       3
% 3.24/0.97  --inst_sel_renew                        solver
% 3.24/0.97  --inst_lit_activity_flag                true
% 3.24/0.97  --inst_restr_to_given                   false
% 3.24/0.97  --inst_activity_threshold               500
% 3.24/0.97  --inst_out_proof                        true
% 3.24/0.97  
% 3.24/0.97  ------ Resolution Options
% 3.24/0.97  
% 3.24/0.97  --resolution_flag                       false
% 3.24/0.97  --res_lit_sel                           adaptive
% 3.24/0.97  --res_lit_sel_side                      none
% 3.24/0.97  --res_ordering                          kbo
% 3.24/0.97  --res_to_prop_solver                    active
% 3.24/0.97  --res_prop_simpl_new                    false
% 3.24/0.97  --res_prop_simpl_given                  true
% 3.24/0.97  --res_passive_queue_type                priority_queues
% 3.24/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.24/0.97  --res_passive_queues_freq               [15;5]
% 3.24/0.97  --res_forward_subs                      full
% 3.24/0.97  --res_backward_subs                     full
% 3.24/0.97  --res_forward_subs_resolution           true
% 3.24/0.97  --res_backward_subs_resolution          true
% 3.24/0.97  --res_orphan_elimination                true
% 3.24/0.97  --res_time_limit                        2.
% 3.24/0.97  --res_out_proof                         true
% 3.24/0.97  
% 3.24/0.97  ------ Superposition Options
% 3.24/0.97  
% 3.24/0.97  --superposition_flag                    true
% 3.24/0.97  --sup_passive_queue_type                priority_queues
% 3.24/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.24/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.24/0.97  --demod_completeness_check              fast
% 3.24/0.97  --demod_use_ground                      true
% 3.24/0.97  --sup_to_prop_solver                    passive
% 3.24/0.97  --sup_prop_simpl_new                    true
% 3.24/0.97  --sup_prop_simpl_given                  true
% 3.24/0.97  --sup_fun_splitting                     false
% 3.24/0.97  --sup_smt_interval                      50000
% 3.24/0.97  
% 3.24/0.97  ------ Superposition Simplification Setup
% 3.24/0.97  
% 3.24/0.97  --sup_indices_passive                   []
% 3.24/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.24/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/0.97  --sup_full_bw                           [BwDemod]
% 3.24/0.97  --sup_immed_triv                        [TrivRules]
% 3.24/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.24/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/0.97  --sup_immed_bw_main                     []
% 3.24/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.24/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/0.97  
% 3.24/0.97  ------ Combination Options
% 3.24/0.97  
% 3.24/0.97  --comb_res_mult                         3
% 3.24/0.97  --comb_sup_mult                         2
% 3.24/0.97  --comb_inst_mult                        10
% 3.24/0.97  
% 3.24/0.97  ------ Debug Options
% 3.24/0.97  
% 3.24/0.97  --dbg_backtrace                         false
% 3.24/0.97  --dbg_dump_prop_clauses                 false
% 3.24/0.97  --dbg_dump_prop_clauses_file            -
% 3.24/0.97  --dbg_out_stat                          false
% 3.24/0.97  
% 3.24/0.97  
% 3.24/0.97  
% 3.24/0.97  
% 3.24/0.97  ------ Proving...
% 3.24/0.97  
% 3.24/0.97  
% 3.24/0.97  % SZS status Theorem for theBenchmark.p
% 3.24/0.97  
% 3.24/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.24/0.97  
% 3.24/0.97  fof(f11,axiom,(
% 3.24/0.97    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 3.24/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/0.97  
% 3.24/0.97  fof(f31,plain,(
% 3.24/0.97    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 3.24/0.97    inference(ennf_transformation,[],[f11])).
% 3.24/0.97  
% 3.24/0.97  fof(f40,plain,(
% 3.24/0.97    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 3.24/0.97    inference(nnf_transformation,[],[f31])).
% 3.24/0.97  
% 3.24/0.97  fof(f64,plain,(
% 3.24/0.97    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 3.24/0.97    inference(cnf_transformation,[],[f40])).
% 3.24/0.97  
% 3.24/0.97  fof(f12,conjecture,(
% 3.24/0.97    ! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 3.24/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/0.97  
% 3.24/0.97  fof(f13,negated_conjecture,(
% 3.24/0.97    ~! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 3.24/0.97    inference(negated_conjecture,[],[f12])).
% 3.24/0.97  
% 3.24/0.97  fof(f32,plain,(
% 3.24/0.97    ? [X0] : ((? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0))) & ~v1_xboole_0(X0))),
% 3.24/0.97    inference(ennf_transformation,[],[f13])).
% 3.24/0.97  
% 3.24/0.97  fof(f33,plain,(
% 3.24/0.97    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0))),
% 3.24/0.97    inference(flattening,[],[f32])).
% 3.24/0.97  
% 3.24/0.97  fof(f43,plain,(
% 3.24/0.97    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) => (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,sK3),k3_xboole_0(X1,sK3)) & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0))))) )),
% 3.24/0.97    introduced(choice_axiom,[])).
% 3.24/0.97  
% 3.24/0.97  fof(f42,plain,(
% 3.24/0.97    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) => (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),sK2,X2),k3_xboole_0(sK2,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(X0))))) )),
% 3.24/0.97    introduced(choice_axiom,[])).
% 3.24/0.97  
% 3.24/0.97  fof(f41,plain,(
% 3.24/0.97    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK1),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK1)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))) & v2_lattice3(k2_yellow_1(sK1)) & ~v1_xboole_0(sK1))),
% 3.24/0.97    introduced(choice_axiom,[])).
% 3.24/0.97  
% 3.24/0.97  fof(f44,plain,(
% 3.24/0.97    ((~r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k3_xboole_0(sK2,sK3)) & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))) & v2_lattice3(k2_yellow_1(sK1)) & ~v1_xboole_0(sK1)),
% 3.24/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f43,f42,f41])).
% 3.24/0.97  
% 3.24/0.97  fof(f66,plain,(
% 3.24/0.97    ~v1_xboole_0(sK1)),
% 3.24/0.97    inference(cnf_transformation,[],[f44])).
% 3.24/0.97  
% 3.24/0.97  fof(f68,plain,(
% 3.24/0.97    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))),
% 3.24/0.97    inference(cnf_transformation,[],[f44])).
% 3.24/0.97  
% 3.24/0.97  fof(f10,axiom,(
% 3.24/0.97    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 3.24/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/0.97  
% 3.24/0.97  fof(f62,plain,(
% 3.24/0.97    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 3.24/0.97    inference(cnf_transformation,[],[f10])).
% 3.24/0.97  
% 3.24/0.97  fof(f69,plain,(
% 3.24/0.97    m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))),
% 3.24/0.97    inference(cnf_transformation,[],[f44])).
% 3.24/0.97  
% 3.24/0.97  fof(f4,axiom,(
% 3.24/0.97    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2))),
% 3.24/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/0.97  
% 3.24/0.97  fof(f24,plain,(
% 3.24/0.97    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 3.24/0.97    inference(ennf_transformation,[],[f4])).
% 3.24/0.97  
% 3.24/0.97  fof(f25,plain,(
% 3.24/0.97    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 3.24/0.97    inference(flattening,[],[f24])).
% 3.24/0.97  
% 3.24/0.97  fof(f49,plain,(
% 3.24/0.97    ( ! [X2,X0,X1] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 3.24/0.97    inference(cnf_transformation,[],[f25])).
% 3.24/0.97  
% 3.24/0.97  fof(f7,axiom,(
% 3.24/0.97    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 3.24/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/0.97  
% 3.24/0.97  fof(f16,plain,(
% 3.24/0.97    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 3.24/0.97    inference(pure_predicate_removal,[],[f7])).
% 3.24/0.97  
% 3.24/0.97  fof(f58,plain,(
% 3.24/0.97    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 3.24/0.97    inference(cnf_transformation,[],[f16])).
% 3.24/0.97  
% 3.24/0.97  fof(f8,axiom,(
% 3.24/0.97    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 3.24/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/0.97  
% 3.24/0.97  fof(f14,plain,(
% 3.24/0.97    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 3.24/0.97    inference(pure_predicate_removal,[],[f8])).
% 3.24/0.97  
% 3.24/0.97  fof(f15,plain,(
% 3.24/0.97    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 3.24/0.97    inference(pure_predicate_removal,[],[f14])).
% 3.24/0.97  
% 3.24/0.97  fof(f60,plain,(
% 3.24/0.97    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 3.24/0.97    inference(cnf_transformation,[],[f15])).
% 3.24/0.97  
% 3.24/0.97  fof(f67,plain,(
% 3.24/0.97    v2_lattice3(k2_yellow_1(sK1))),
% 3.24/0.97    inference(cnf_transformation,[],[f44])).
% 3.24/0.97  
% 3.24/0.97  fof(f1,axiom,(
% 3.24/0.97    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 3.24/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/0.97  
% 3.24/0.97  fof(f18,plain,(
% 3.24/0.97    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 3.24/0.97    inference(ennf_transformation,[],[f1])).
% 3.24/0.97  
% 3.24/0.97  fof(f19,plain,(
% 3.24/0.97    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 3.24/0.97    inference(flattening,[],[f18])).
% 3.24/0.97  
% 3.24/0.97  fof(f45,plain,(
% 3.24/0.97    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.24/0.97    inference(cnf_transformation,[],[f19])).
% 3.24/0.97  
% 3.24/0.97  fof(f70,plain,(
% 3.24/0.97    ~r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k3_xboole_0(sK2,sK3))),
% 3.24/0.97    inference(cnf_transformation,[],[f44])).
% 3.24/0.97  
% 3.24/0.97  fof(f2,axiom,(
% 3.24/0.97    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 3.24/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/0.97  
% 3.24/0.97  fof(f20,plain,(
% 3.24/0.97    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.24/0.97    inference(ennf_transformation,[],[f2])).
% 3.24/0.97  
% 3.24/0.97  fof(f21,plain,(
% 3.24/0.97    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.24/0.97    inference(flattening,[],[f20])).
% 3.24/0.97  
% 3.24/0.97  fof(f34,plain,(
% 3.24/0.97    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.24/0.97    inference(nnf_transformation,[],[f21])).
% 3.24/0.97  
% 3.24/0.97  fof(f47,plain,(
% 3.24/0.97    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.24/0.97    inference(cnf_transformation,[],[f34])).
% 3.24/0.97  
% 3.24/0.97  fof(f59,plain,(
% 3.24/0.97    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 3.24/0.97    inference(cnf_transformation,[],[f15])).
% 3.24/0.97  
% 3.24/0.97  fof(f3,axiom,(
% 3.24/0.97    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 3.24/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/0.97  
% 3.24/0.97  fof(f22,plain,(
% 3.24/0.97    ! [X0,X1,X2] : (m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 3.24/0.97    inference(ennf_transformation,[],[f3])).
% 3.24/0.97  
% 3.24/0.97  fof(f23,plain,(
% 3.24/0.97    ! [X0,X1,X2] : (m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 3.24/0.97    inference(flattening,[],[f22])).
% 3.24/0.97  
% 3.24/0.97  fof(f48,plain,(
% 3.24/0.97    ( ! [X2,X0,X1] : (m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 3.24/0.97    inference(cnf_transformation,[],[f23])).
% 3.24/0.97  
% 3.24/0.97  fof(f6,axiom,(
% 3.24/0.97    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k12_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 3.24/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/0.97  
% 3.24/0.97  fof(f28,plain,(
% 3.24/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k12_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 3.24/0.97    inference(ennf_transformation,[],[f6])).
% 3.24/0.97  
% 3.24/0.97  fof(f29,plain,(
% 3.24/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k12_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 3.24/0.97    inference(flattening,[],[f28])).
% 3.24/0.97  
% 3.24/0.97  fof(f35,plain,(
% 3.24/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k12_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k12_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 3.24/0.97    inference(nnf_transformation,[],[f29])).
% 3.24/0.97  
% 3.24/0.97  fof(f36,plain,(
% 3.24/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k12_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k12_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 3.24/0.97    inference(flattening,[],[f35])).
% 3.24/0.97  
% 3.24/0.97  fof(f37,plain,(
% 3.24/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k12_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k12_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 3.24/0.97    inference(rectify,[],[f36])).
% 3.24/0.97  
% 3.24/0.97  fof(f38,plain,(
% 3.24/0.97    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK0(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK0(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK0(X0,X1,X2,X3),X1) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))))),
% 3.24/0.97    introduced(choice_axiom,[])).
% 3.24/0.97  
% 3.24/0.97  fof(f39,plain,(
% 3.24/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k12_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,sK0(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK0(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK0(X0,X1,X2,X3),X1) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k12_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 3.24/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 3.24/0.97  
% 3.24/0.97  fof(f51,plain,(
% 3.24/0.97    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X3,X1) | k12_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 3.24/0.97    inference(cnf_transformation,[],[f39])).
% 3.24/0.97  
% 3.24/0.97  fof(f73,plain,(
% 3.24/0.97    ( ! [X2,X0,X1] : (r1_orders_2(X0,k12_lattice3(X0,X1,X2),X1) | ~m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 3.24/0.97    inference(equality_resolution,[],[f51])).
% 3.24/0.97  
% 3.24/0.97  fof(f52,plain,(
% 3.24/0.97    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X3,X2) | k12_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 3.24/0.97    inference(cnf_transformation,[],[f39])).
% 3.24/0.97  
% 3.24/0.97  fof(f72,plain,(
% 3.24/0.97    ( ! [X2,X0,X1] : (r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2) | ~m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 3.24/0.97    inference(equality_resolution,[],[f52])).
% 3.24/0.97  
% 3.24/0.97  fof(f9,axiom,(
% 3.24/0.97    ! [X0] : (~v1_xboole_0(X0) => (v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))))),
% 3.24/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/0.97  
% 3.24/0.97  fof(f17,plain,(
% 3.24/0.97    ! [X0] : (~v1_xboole_0(X0) => ~v2_struct_0(k2_yellow_1(X0)))),
% 3.24/0.97    inference(pure_predicate_removal,[],[f9])).
% 3.24/0.97  
% 3.24/0.97  fof(f30,plain,(
% 3.24/0.97    ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0))),
% 3.24/0.97    inference(ennf_transformation,[],[f17])).
% 3.24/0.97  
% 3.24/0.97  fof(f61,plain,(
% 3.24/0.97    ( ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 3.24/0.97    inference(cnf_transformation,[],[f30])).
% 3.24/0.97  
% 3.24/0.97  cnf(c_20,plain,
% 3.24/0.97      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.24/0.97      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.24/0.97      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.24/0.97      | r1_tarski(X1,X2)
% 3.24/0.97      | v1_xboole_0(X0) ),
% 3.24/0.97      inference(cnf_transformation,[],[f64]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_25,negated_conjecture,
% 3.24/0.97      ( ~ v1_xboole_0(sK1) ),
% 3.24/0.97      inference(cnf_transformation,[],[f66]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_273,plain,
% 3.24/0.97      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.24/0.97      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.24/0.97      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.24/0.97      | r1_tarski(X1,X2)
% 3.24/0.97      | sK1 != X0 ),
% 3.24/0.97      inference(resolution_lifted,[status(thm)],[c_20,c_25]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_274,plain,
% 3.24/0.97      ( ~ r3_orders_2(k2_yellow_1(sK1),X0,X1)
% 3.24/0.97      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 3.24/0.97      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
% 3.24/0.97      | r1_tarski(X0,X1) ),
% 3.24/0.97      inference(unflattening,[status(thm)],[c_273]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_2798,plain,
% 3.24/0.97      ( ~ r3_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),sK2,sK3),X0)
% 3.24/0.97      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 3.24/0.97      | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 3.24/0.97      | r1_tarski(k12_lattice3(k2_yellow_1(sK1),sK2,sK3),X0) ),
% 3.24/0.97      inference(instantiation,[status(thm)],[c_274]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_8079,plain,
% 3.24/0.97      ( ~ r3_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2)
% 3.24/0.97      | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 3.24/0.97      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
% 3.24/0.97      | r1_tarski(k12_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2) ),
% 3.24/0.97      inference(instantiation,[status(thm)],[c_2798]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_8076,plain,
% 3.24/0.97      ( ~ r3_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3)
% 3.24/0.97      | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 3.24/0.97      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
% 3.24/0.97      | r1_tarski(k12_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3) ),
% 3.24/0.97      inference(instantiation,[status(thm)],[c_2798]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_23,negated_conjecture,
% 3.24/0.97      ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
% 3.24/0.97      inference(cnf_transformation,[],[f68]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_2110,plain,
% 3.24/0.97      ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
% 3.24/0.97      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_18,plain,
% 3.24/0.97      ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
% 3.24/0.97      inference(cnf_transformation,[],[f62]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_2122,plain,
% 3.24/0.97      ( m1_subset_1(sK2,sK1) = iProver_top ),
% 3.24/0.97      inference(demodulation,[status(thm)],[c_2110,c_18]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_22,negated_conjecture,
% 3.24/0.97      ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) ),
% 3.24/0.97      inference(cnf_transformation,[],[f69]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_2111,plain,
% 3.24/0.97      ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
% 3.24/0.97      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_2125,plain,
% 3.24/0.97      ( m1_subset_1(sK3,sK1) = iProver_top ),
% 3.24/0.97      inference(demodulation,[status(thm)],[c_2111,c_18]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_4,plain,
% 3.24/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.24/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.24/0.97      | ~ v5_orders_2(X1)
% 3.24/0.97      | ~ v2_lattice3(X1)
% 3.24/0.97      | ~ l1_orders_2(X1)
% 3.24/0.97      | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0) ),
% 3.24/0.97      inference(cnf_transformation,[],[f49]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_13,plain,
% 3.24/0.97      ( l1_orders_2(k2_yellow_1(X0)) ),
% 3.24/0.97      inference(cnf_transformation,[],[f58]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_771,plain,
% 3.24/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.24/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.24/0.97      | ~ v5_orders_2(X1)
% 3.24/0.97      | ~ v2_lattice3(X1)
% 3.24/0.97      | k11_lattice3(X1,X2,X0) = k12_lattice3(X1,X2,X0)
% 3.24/0.97      | k2_yellow_1(X3) != X1 ),
% 3.24/0.97      inference(resolution_lifted,[status(thm)],[c_4,c_13]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_772,plain,
% 3.24/0.97      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
% 3.24/0.97      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
% 3.24/0.97      | ~ v5_orders_2(k2_yellow_1(X1))
% 3.24/0.97      | ~ v2_lattice3(k2_yellow_1(X1))
% 3.24/0.97      | k11_lattice3(k2_yellow_1(X1),X0,X2) = k12_lattice3(k2_yellow_1(X1),X0,X2) ),
% 3.24/0.97      inference(unflattening,[status(thm)],[c_771]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_14,plain,
% 3.24/0.97      ( v5_orders_2(k2_yellow_1(X0)) ),
% 3.24/0.97      inference(cnf_transformation,[],[f60]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_786,plain,
% 3.24/0.97      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
% 3.24/0.97      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
% 3.24/0.97      | ~ v2_lattice3(k2_yellow_1(X1))
% 3.24/0.97      | k11_lattice3(k2_yellow_1(X1),X0,X2) = k12_lattice3(k2_yellow_1(X1),X0,X2) ),
% 3.24/0.97      inference(forward_subsumption_resolution,
% 3.24/0.97                [status(thm)],
% 3.24/0.97                [c_772,c_14]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_2097,plain,
% 3.24/0.97      ( k11_lattice3(k2_yellow_1(X0),X1,X2) = k12_lattice3(k2_yellow_1(X0),X1,X2)
% 3.24/0.97      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.24/0.97      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.24/0.97      | v2_lattice3(k2_yellow_1(X0)) != iProver_top ),
% 3.24/0.97      inference(predicate_to_equality,[status(thm)],[c_786]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_2181,plain,
% 3.24/0.97      ( k11_lattice3(k2_yellow_1(X0),X1,X2) = k12_lattice3(k2_yellow_1(X0),X1,X2)
% 3.24/0.97      | m1_subset_1(X2,X0) != iProver_top
% 3.24/0.97      | m1_subset_1(X1,X0) != iProver_top
% 3.24/0.97      | v2_lattice3(k2_yellow_1(X0)) != iProver_top ),
% 3.24/0.97      inference(light_normalisation,[status(thm)],[c_2097,c_18]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_3425,plain,
% 3.24/0.97      ( k11_lattice3(k2_yellow_1(sK1),X0,sK3) = k12_lattice3(k2_yellow_1(sK1),X0,sK3)
% 3.24/0.97      | m1_subset_1(X0,sK1) != iProver_top
% 3.24/0.97      | v2_lattice3(k2_yellow_1(sK1)) != iProver_top ),
% 3.24/0.97      inference(superposition,[status(thm)],[c_2125,c_2181]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_24,negated_conjecture,
% 3.24/0.97      ( v2_lattice3(k2_yellow_1(sK1)) ),
% 3.24/0.97      inference(cnf_transformation,[],[f67]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_27,plain,
% 3.24/0.97      ( v2_lattice3(k2_yellow_1(sK1)) = iProver_top ),
% 3.24/0.97      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_4494,plain,
% 3.24/0.97      ( m1_subset_1(X0,sK1) != iProver_top
% 3.24/0.97      | k11_lattice3(k2_yellow_1(sK1),X0,sK3) = k12_lattice3(k2_yellow_1(sK1),X0,sK3) ),
% 3.24/0.97      inference(global_propositional_subsumption,
% 3.24/0.97                [status(thm)],
% 3.24/0.97                [c_3425,c_27]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_4495,plain,
% 3.24/0.97      ( k11_lattice3(k2_yellow_1(sK1),X0,sK3) = k12_lattice3(k2_yellow_1(sK1),X0,sK3)
% 3.24/0.97      | m1_subset_1(X0,sK1) != iProver_top ),
% 3.24/0.97      inference(renaming,[status(thm)],[c_4494]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_4502,plain,
% 3.24/0.97      ( k11_lattice3(k2_yellow_1(sK1),sK2,sK3) = k12_lattice3(k2_yellow_1(sK1),sK2,sK3) ),
% 3.24/0.97      inference(superposition,[status(thm)],[c_2122,c_4495]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_0,plain,
% 3.24/0.97      ( ~ r1_tarski(X0,X1)
% 3.24/0.97      | ~ r1_tarski(X0,X2)
% 3.24/0.97      | r1_tarski(X0,k3_xboole_0(X2,X1)) ),
% 3.24/0.97      inference(cnf_transformation,[],[f45]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_2113,plain,
% 3.24/0.97      ( r1_tarski(X0,X1) != iProver_top
% 3.24/0.97      | r1_tarski(X0,X2) != iProver_top
% 3.24/0.97      | r1_tarski(X0,k3_xboole_0(X2,X1)) = iProver_top ),
% 3.24/0.97      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_21,negated_conjecture,
% 3.24/0.97      ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k3_xboole_0(sK2,sK3)) ),
% 3.24/0.97      inference(cnf_transformation,[],[f70]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_2112,plain,
% 3.24/0.97      ( r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k3_xboole_0(sK2,sK3)) != iProver_top ),
% 3.24/0.97      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_3043,plain,
% 3.24/0.97      ( r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3) != iProver_top
% 3.24/0.97      | r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2) != iProver_top ),
% 3.24/0.97      inference(superposition,[status(thm)],[c_2113,c_2112]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_4521,plain,
% 3.24/0.97      ( r1_tarski(k12_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3) != iProver_top
% 3.24/0.97      | r1_tarski(k12_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2) != iProver_top ),
% 3.24/0.97      inference(demodulation,[status(thm)],[c_4502,c_3043]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_4529,plain,
% 3.24/0.97      ( ~ r1_tarski(k12_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3)
% 3.24/0.97      | ~ r1_tarski(k12_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2) ),
% 3.24/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_4521]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_1,plain,
% 3.24/0.97      ( ~ r1_orders_2(X0,X1,X2)
% 3.24/0.97      | r3_orders_2(X0,X1,X2)
% 3.24/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.24/0.97      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.24/0.97      | v2_struct_0(X0)
% 3.24/0.97      | ~ v3_orders_2(X0)
% 3.24/0.97      | ~ l1_orders_2(X0) ),
% 3.24/0.97      inference(cnf_transformation,[],[f47]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_15,plain,
% 3.24/0.97      ( v3_orders_2(k2_yellow_1(X0)) ),
% 3.24/0.97      inference(cnf_transformation,[],[f59]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_355,plain,
% 3.24/0.97      ( ~ r1_orders_2(X0,X1,X2)
% 3.24/0.97      | r3_orders_2(X0,X1,X2)
% 3.24/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.24/0.97      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.24/0.97      | v2_struct_0(X0)
% 3.24/0.97      | ~ l1_orders_2(X0)
% 3.24/0.97      | k2_yellow_1(X3) != X0 ),
% 3.24/0.97      inference(resolution_lifted,[status(thm)],[c_1,c_15]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_356,plain,
% 3.24/0.97      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 3.24/0.97      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.24/0.97      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.24/0.97      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.24/0.97      | v2_struct_0(k2_yellow_1(X0))
% 3.24/0.97      | ~ l1_orders_2(k2_yellow_1(X0)) ),
% 3.24/0.97      inference(unflattening,[status(thm)],[c_355]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_360,plain,
% 3.24/0.97      ( v2_struct_0(k2_yellow_1(X0))
% 3.24/0.97      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.24/0.97      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.24/0.97      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.24/0.97      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2) ),
% 3.24/0.97      inference(global_propositional_subsumption,
% 3.24/0.97                [status(thm)],
% 3.24/0.97                [c_356,c_13]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_361,plain,
% 3.24/0.97      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 3.24/0.97      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.24/0.97      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.24/0.97      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.24/0.97      | v2_struct_0(k2_yellow_1(X0)) ),
% 3.24/0.97      inference(renaming,[status(thm)],[c_360]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_2464,plain,
% 3.24/0.97      ( ~ r1_orders_2(k2_yellow_1(sK1),X0,sK2)
% 3.24/0.97      | r3_orders_2(k2_yellow_1(sK1),X0,sK2)
% 3.24/0.97      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 3.24/0.97      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
% 3.24/0.97      | v2_struct_0(k2_yellow_1(sK1)) ),
% 3.24/0.97      inference(instantiation,[status(thm)],[c_361]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_3982,plain,
% 3.24/0.97      ( ~ r1_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2)
% 3.24/0.97      | r3_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2)
% 3.24/0.97      | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 3.24/0.97      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
% 3.24/0.97      | v2_struct_0(k2_yellow_1(sK1)) ),
% 3.24/0.97      inference(instantiation,[status(thm)],[c_2464]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_2459,plain,
% 3.24/0.97      ( ~ r1_orders_2(k2_yellow_1(sK1),X0,sK3)
% 3.24/0.97      | r3_orders_2(k2_yellow_1(sK1),X0,sK3)
% 3.24/0.97      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 3.24/0.97      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
% 3.24/0.97      | v2_struct_0(k2_yellow_1(sK1)) ),
% 3.24/0.97      inference(instantiation,[status(thm)],[c_361]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_3119,plain,
% 3.24/0.97      ( ~ r1_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3)
% 3.24/0.97      | r3_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3)
% 3.24/0.97      | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 3.24/0.97      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
% 3.24/0.97      | v2_struct_0(k2_yellow_1(sK1)) ),
% 3.24/0.97      inference(instantiation,[status(thm)],[c_2459]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_3,plain,
% 3.24/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.24/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.24/0.97      | m1_subset_1(k12_lattice3(X1,X2,X0),u1_struct_0(X1))
% 3.24/0.97      | ~ v5_orders_2(X1)
% 3.24/0.97      | ~ v2_lattice3(X1)
% 3.24/0.97      | ~ l1_orders_2(X1) ),
% 3.24/0.97      inference(cnf_transformation,[],[f48]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_794,plain,
% 3.24/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.24/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.24/0.97      | m1_subset_1(k12_lattice3(X1,X2,X0),u1_struct_0(X1))
% 3.24/0.97      | ~ v5_orders_2(X1)
% 3.24/0.97      | ~ v2_lattice3(X1)
% 3.24/0.97      | k2_yellow_1(X3) != X1 ),
% 3.24/0.97      inference(resolution_lifted,[status(thm)],[c_3,c_13]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_795,plain,
% 3.24/0.97      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
% 3.24/0.97      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
% 3.24/0.97      | m1_subset_1(k12_lattice3(k2_yellow_1(X1),X0,X2),u1_struct_0(k2_yellow_1(X1)))
% 3.24/0.97      | ~ v5_orders_2(k2_yellow_1(X1))
% 3.24/0.97      | ~ v2_lattice3(k2_yellow_1(X1)) ),
% 3.24/0.97      inference(unflattening,[status(thm)],[c_794]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_809,plain,
% 3.24/0.97      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
% 3.24/0.97      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
% 3.24/0.97      | m1_subset_1(k12_lattice3(k2_yellow_1(X1),X0,X2),u1_struct_0(k2_yellow_1(X1)))
% 3.24/0.97      | ~ v2_lattice3(k2_yellow_1(X1)) ),
% 3.24/0.97      inference(forward_subsumption_resolution,
% 3.24/0.97                [status(thm)],
% 3.24/0.97                [c_795,c_14]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_12,plain,
% 3.24/0.97      ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X1)
% 3.24/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.24/0.97      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.24/0.97      | ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
% 3.24/0.97      | ~ v5_orders_2(X0)
% 3.24/0.97      | ~ v2_lattice3(X0)
% 3.24/0.97      | ~ l1_orders_2(X0) ),
% 3.24/0.97      inference(cnf_transformation,[],[f73]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_522,plain,
% 3.24/0.97      ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X1)
% 3.24/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.24/0.97      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.24/0.97      | ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
% 3.24/0.97      | ~ v5_orders_2(X0)
% 3.24/0.97      | ~ v2_lattice3(X0)
% 3.24/0.97      | k2_yellow_1(X3) != X0 ),
% 3.24/0.97      inference(resolution_lifted,[status(thm)],[c_12,c_13]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_523,plain,
% 3.24/0.97      ( r1_orders_2(k2_yellow_1(X0),k12_lattice3(k2_yellow_1(X0),X1,X2),X1)
% 3.24/0.97      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.24/0.97      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.24/0.97      | ~ m1_subset_1(k12_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
% 3.24/0.97      | ~ v5_orders_2(k2_yellow_1(X0))
% 3.24/0.97      | ~ v2_lattice3(k2_yellow_1(X0)) ),
% 3.24/0.97      inference(unflattening,[status(thm)],[c_522]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_527,plain,
% 3.24/0.97      ( ~ m1_subset_1(k12_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
% 3.24/0.97      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.24/0.97      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.24/0.97      | r1_orders_2(k2_yellow_1(X0),k12_lattice3(k2_yellow_1(X0),X1,X2),X1)
% 3.24/0.97      | ~ v2_lattice3(k2_yellow_1(X0)) ),
% 3.24/0.97      inference(global_propositional_subsumption,
% 3.24/0.97                [status(thm)],
% 3.24/0.97                [c_523,c_14]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_528,plain,
% 3.24/0.97      ( r1_orders_2(k2_yellow_1(X0),k12_lattice3(k2_yellow_1(X0),X1,X2),X1)
% 3.24/0.97      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.24/0.97      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.24/0.97      | ~ m1_subset_1(k12_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
% 3.24/0.97      | ~ v2_lattice3(k2_yellow_1(X0)) ),
% 3.24/0.97      inference(renaming,[status(thm)],[c_527]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_814,plain,
% 3.24/0.97      ( r1_orders_2(k2_yellow_1(X0),k12_lattice3(k2_yellow_1(X0),X1,X2),X1)
% 3.24/0.97      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.24/0.97      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.24/0.97      | ~ v2_lattice3(k2_yellow_1(X0)) ),
% 3.24/0.97      inference(backward_subsumption_resolution,
% 3.24/0.97                [status(thm)],
% 3.24/0.97                [c_809,c_528]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_2435,plain,
% 3.24/0.97      ( r1_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),X0,sK3),X0)
% 3.24/0.97      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 3.24/0.97      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
% 3.24/0.97      | ~ v2_lattice3(k2_yellow_1(sK1)) ),
% 3.24/0.97      inference(instantiation,[status(thm)],[c_814]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_3075,plain,
% 3.24/0.97      ( r1_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2)
% 3.24/0.97      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
% 3.24/0.97      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
% 3.24/0.97      | ~ v2_lattice3(k2_yellow_1(sK1)) ),
% 3.24/0.97      inference(instantiation,[status(thm)],[c_2435]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_11,plain,
% 3.24/0.97      ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2)
% 3.24/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.24/0.97      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.24/0.97      | ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
% 3.24/0.97      | ~ v5_orders_2(X0)
% 3.24/0.97      | ~ v2_lattice3(X0)
% 3.24/0.97      | ~ l1_orders_2(X0) ),
% 3.24/0.97      inference(cnf_transformation,[],[f72]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_549,plain,
% 3.24/0.97      ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2)
% 3.24/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.24/0.97      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.24/0.97      | ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
% 3.24/0.97      | ~ v5_orders_2(X0)
% 3.24/0.97      | ~ v2_lattice3(X0)
% 3.24/0.97      | k2_yellow_1(X3) != X0 ),
% 3.24/0.97      inference(resolution_lifted,[status(thm)],[c_11,c_13]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_550,plain,
% 3.24/0.97      ( r1_orders_2(k2_yellow_1(X0),k12_lattice3(k2_yellow_1(X0),X1,X2),X2)
% 3.24/0.97      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.24/0.97      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.24/0.97      | ~ m1_subset_1(k12_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
% 3.24/0.97      | ~ v5_orders_2(k2_yellow_1(X0))
% 3.24/0.97      | ~ v2_lattice3(k2_yellow_1(X0)) ),
% 3.24/0.97      inference(unflattening,[status(thm)],[c_549]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_552,plain,
% 3.24/0.97      ( ~ m1_subset_1(k12_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
% 3.24/0.97      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.24/0.97      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.24/0.97      | r1_orders_2(k2_yellow_1(X0),k12_lattice3(k2_yellow_1(X0),X1,X2),X2)
% 3.24/0.97      | ~ v2_lattice3(k2_yellow_1(X0)) ),
% 3.24/0.97      inference(global_propositional_subsumption,
% 3.24/0.97                [status(thm)],
% 3.24/0.97                [c_550,c_14]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_553,plain,
% 3.24/0.97      ( r1_orders_2(k2_yellow_1(X0),k12_lattice3(k2_yellow_1(X0),X1,X2),X2)
% 3.24/0.97      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.24/0.97      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.24/0.97      | ~ m1_subset_1(k12_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
% 3.24/0.97      | ~ v2_lattice3(k2_yellow_1(X0)) ),
% 3.24/0.97      inference(renaming,[status(thm)],[c_552]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_813,plain,
% 3.24/0.97      ( r1_orders_2(k2_yellow_1(X0),k12_lattice3(k2_yellow_1(X0),X1,X2),X2)
% 3.24/0.97      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.24/0.97      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.24/0.97      | ~ v2_lattice3(k2_yellow_1(X0)) ),
% 3.24/0.97      inference(backward_subsumption_resolution,
% 3.24/0.97                [status(thm)],
% 3.24/0.97                [c_809,c_553]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_2425,plain,
% 3.24/0.97      ( r1_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),X0,sK3),sK3)
% 3.24/0.97      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 3.24/0.97      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
% 3.24/0.97      | ~ v2_lattice3(k2_yellow_1(sK1)) ),
% 3.24/0.97      inference(instantiation,[status(thm)],[c_813]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_2910,plain,
% 3.24/0.97      ( r1_orders_2(k2_yellow_1(sK1),k12_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3)
% 3.24/0.97      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
% 3.24/0.97      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
% 3.24/0.97      | ~ v2_lattice3(k2_yellow_1(sK1)) ),
% 3.24/0.97      inference(instantiation,[status(thm)],[c_2425]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_2420,plain,
% 3.24/0.97      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 3.24/0.97      | m1_subset_1(k12_lattice3(k2_yellow_1(sK1),sK2,X0),u1_struct_0(k2_yellow_1(sK1)))
% 3.24/0.97      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
% 3.24/0.97      | ~ v2_lattice3(k2_yellow_1(sK1)) ),
% 3.24/0.97      inference(instantiation,[status(thm)],[c_809]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_2571,plain,
% 3.24/0.97      ( m1_subset_1(k12_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 3.24/0.97      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
% 3.24/0.97      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
% 3.24/0.97      | ~ v2_lattice3(k2_yellow_1(sK1)) ),
% 3.24/0.97      inference(instantiation,[status(thm)],[c_2420]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_16,plain,
% 3.24/0.97      ( v1_xboole_0(X0) | ~ v2_struct_0(k2_yellow_1(X0)) ),
% 3.24/0.97      inference(cnf_transformation,[],[f61]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(c_40,plain,
% 3.24/0.97      ( v1_xboole_0(sK1) | ~ v2_struct_0(k2_yellow_1(sK1)) ),
% 3.24/0.97      inference(instantiation,[status(thm)],[c_16]) ).
% 3.24/0.97  
% 3.24/0.97  cnf(contradiction,plain,
% 3.24/0.97      ( $false ),
% 3.24/0.97      inference(minisat,
% 3.24/0.97                [status(thm)],
% 3.24/0.97                [c_8079,c_8076,c_4529,c_3982,c_3119,c_3075,c_2910,c_2571,
% 3.24/0.97                 c_40,c_22,c_23,c_24,c_25]) ).
% 3.24/0.97  
% 3.24/0.97  
% 3.24/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.24/0.97  
% 3.24/0.97  ------                               Statistics
% 3.24/0.97  
% 3.24/0.97  ------ General
% 3.24/0.97  
% 3.24/0.97  abstr_ref_over_cycles:                  0
% 3.24/0.97  abstr_ref_under_cycles:                 0
% 3.24/0.97  gc_basic_clause_elim:                   0
% 3.24/0.97  forced_gc_time:                         0
% 3.24/0.97  parsing_time:                           0.018
% 3.24/0.97  unif_index_cands_time:                  0.
% 3.24/0.97  unif_index_add_time:                    0.
% 3.24/0.97  orderings_time:                         0.
% 3.24/0.97  out_proof_time:                         0.012
% 3.24/0.97  total_time:                             0.386
% 3.24/0.97  num_of_symbols:                         52
% 3.24/0.97  num_of_terms:                           8199
% 3.24/0.97  
% 3.24/0.97  ------ Preprocessing
% 3.24/0.97  
% 3.24/0.97  num_of_splits:                          0
% 3.24/0.97  num_of_split_atoms:                     0
% 3.24/0.97  num_of_reused_defs:                     0
% 3.24/0.97  num_eq_ax_congr_red:                    27
% 3.24/0.97  num_of_sem_filtered_clauses:            1
% 3.24/0.97  num_of_subtypes:                        0
% 3.24/0.97  monotx_restored_types:                  0
% 3.24/0.97  sat_num_of_epr_types:                   0
% 3.24/0.97  sat_num_of_non_cyclic_types:            0
% 3.24/0.97  sat_guarded_non_collapsed_types:        0
% 3.24/0.97  num_pure_diseq_elim:                    0
% 3.24/0.97  simp_replaced_by:                       0
% 3.24/0.97  res_preprocessed:                       123
% 3.24/0.97  prep_upred:                             0
% 3.24/0.97  prep_unflattend:                        23
% 3.24/0.97  smt_new_axioms:                         0
% 3.24/0.97  pred_elim_cands:                        6
% 3.24/0.97  pred_elim:                              4
% 3.24/0.97  pred_elim_cl:                           4
% 3.24/0.97  pred_elim_cycles:                       10
% 3.24/0.97  merged_defs:                            0
% 3.24/0.97  merged_defs_ncl:                        0
% 3.24/0.97  bin_hyper_res:                          0
% 3.24/0.97  prep_cycles:                            4
% 3.24/0.97  pred_elim_time:                         0.036
% 3.24/0.97  splitting_time:                         0.
% 3.24/0.97  sem_filter_time:                        0.
% 3.24/0.97  monotx_time:                            0.001
% 3.24/0.97  subtype_inf_time:                       0.
% 3.24/0.97  
% 3.24/0.97  ------ Problem properties
% 3.24/0.97  
% 3.24/0.97  clauses:                                22
% 3.24/0.97  conjectures:                            4
% 3.24/0.97  epr:                                    0
% 3.24/0.97  horn:                                   17
% 3.24/0.97  ground:                                 5
% 3.24/0.97  unary:                                  7
% 3.24/0.97  binary:                                 0
% 3.24/0.97  lits:                                   88
% 3.24/0.97  lits_eq:                                8
% 3.24/0.97  fd_pure:                                0
% 3.24/0.97  fd_pseudo:                              0
% 3.24/0.97  fd_cond:                                0
% 3.24/0.97  fd_pseudo_cond:                         4
% 3.24/0.97  ac_symbols:                             0
% 3.24/0.97  
% 3.24/0.97  ------ Propositional Solver
% 3.24/0.97  
% 3.24/0.97  prop_solver_calls:                      28
% 3.24/0.97  prop_fast_solver_calls:                 1470
% 3.24/0.97  smt_solver_calls:                       0
% 3.24/0.97  smt_fast_solver_calls:                  0
% 3.24/0.97  prop_num_of_clauses:                    3276
% 3.24/0.97  prop_preprocess_simplified:             8098
% 3.24/0.97  prop_fo_subsumed:                       19
% 3.24/0.97  prop_solver_time:                       0.
% 3.24/0.97  smt_solver_time:                        0.
% 3.24/0.97  smt_fast_solver_time:                   0.
% 3.24/0.97  prop_fast_solver_time:                  0.
% 3.24/0.97  prop_unsat_core_time:                   0.
% 3.24/0.97  
% 3.24/0.97  ------ QBF
% 3.24/0.97  
% 3.24/0.97  qbf_q_res:                              0
% 3.24/0.97  qbf_num_tautologies:                    0
% 3.24/0.97  qbf_prep_cycles:                        0
% 3.24/0.97  
% 3.24/0.97  ------ BMC1
% 3.24/0.97  
% 3.24/0.97  bmc1_current_bound:                     -1
% 3.24/0.97  bmc1_last_solved_bound:                 -1
% 3.24/0.97  bmc1_unsat_core_size:                   -1
% 3.24/0.97  bmc1_unsat_core_parents_size:           -1
% 3.24/0.97  bmc1_merge_next_fun:                    0
% 3.24/0.97  bmc1_unsat_core_clauses_time:           0.
% 3.24/0.97  
% 3.24/0.97  ------ Instantiation
% 3.24/0.97  
% 3.24/0.97  inst_num_of_clauses:                    844
% 3.24/0.97  inst_num_in_passive:                    358
% 3.24/0.97  inst_num_in_active:                     306
% 3.24/0.97  inst_num_in_unprocessed:                179
% 3.24/0.97  inst_num_of_loops:                      332
% 3.24/0.97  inst_num_of_learning_restarts:          0
% 3.24/0.97  inst_num_moves_active_passive:          24
% 3.24/0.97  inst_lit_activity:                      0
% 3.24/0.97  inst_lit_activity_moves:                1
% 3.24/0.97  inst_num_tautologies:                   0
% 3.24/0.97  inst_num_prop_implied:                  0
% 3.24/0.97  inst_num_existing_simplified:           0
% 3.24/0.97  inst_num_eq_res_simplified:             0
% 3.24/0.97  inst_num_child_elim:                    0
% 3.24/0.97  inst_num_of_dismatching_blockings:      230
% 3.24/0.97  inst_num_of_non_proper_insts:           398
% 3.24/0.97  inst_num_of_duplicates:                 0
% 3.24/0.97  inst_inst_num_from_inst_to_res:         0
% 3.24/0.97  inst_dismatching_checking_time:         0.
% 3.24/0.97  
% 3.24/0.97  ------ Resolution
% 3.24/0.97  
% 3.24/0.97  res_num_of_clauses:                     0
% 3.24/0.97  res_num_in_passive:                     0
% 3.24/0.97  res_num_in_active:                      0
% 3.24/0.97  res_num_of_loops:                       127
% 3.24/0.97  res_forward_subset_subsumed:            4
% 3.24/0.97  res_backward_subset_subsumed:           0
% 3.24/0.97  res_forward_subsumed:                   0
% 3.24/0.97  res_backward_subsumed:                  0
% 3.24/0.97  res_forward_subsumption_resolution:     3
% 3.24/0.97  res_backward_subsumption_resolution:    2
% 3.24/0.97  res_clause_to_clause_subsumption:       879
% 3.24/0.97  res_orphan_elimination:                 0
% 3.24/0.97  res_tautology_del:                      11
% 3.24/0.97  res_num_eq_res_simplified:              0
% 3.24/0.97  res_num_sel_changes:                    0
% 3.24/0.97  res_moves_from_active_to_pass:          0
% 3.24/0.97  
% 3.24/0.97  ------ Superposition
% 3.24/0.97  
% 3.24/0.97  sup_time_total:                         0.
% 3.24/0.97  sup_time_generating:                    0.
% 3.24/0.97  sup_time_sim_full:                      0.
% 3.24/0.97  sup_time_sim_immed:                     0.
% 3.24/0.97  
% 3.24/0.97  sup_num_of_clauses:                     115
% 3.24/0.97  sup_num_in_active:                      60
% 3.24/0.97  sup_num_in_passive:                     55
% 3.24/0.97  sup_num_of_loops:                       66
% 3.24/0.97  sup_fw_superposition:                   92
% 3.24/0.97  sup_bw_superposition:                   14
% 3.24/0.97  sup_immediate_simplified:               16
% 3.24/0.97  sup_given_eliminated:                   0
% 3.24/0.97  comparisons_done:                       0
% 3.24/0.97  comparisons_avoided:                    0
% 3.24/0.97  
% 3.24/0.97  ------ Simplifications
% 3.24/0.97  
% 3.24/0.97  
% 3.24/0.97  sim_fw_subset_subsumed:                 1
% 3.24/0.97  sim_bw_subset_subsumed:                 0
% 3.24/0.97  sim_fw_subsumed:                        4
% 3.24/0.97  sim_bw_subsumed:                        0
% 3.24/0.97  sim_fw_subsumption_res:                 1
% 3.24/0.97  sim_bw_subsumption_res:                 0
% 3.24/0.97  sim_tautology_del:                      1
% 3.24/0.98  sim_eq_tautology_del:                   4
% 3.24/0.98  sim_eq_res_simp:                        0
% 3.24/0.98  sim_fw_demodulated:                     5
% 3.24/0.98  sim_bw_demodulated:                     6
% 3.24/0.98  sim_light_normalised:                   22
% 3.24/0.98  sim_joinable_taut:                      0
% 3.24/0.98  sim_joinable_simp:                      0
% 3.24/0.98  sim_ac_normalised:                      0
% 3.24/0.98  sim_smt_subsumption:                    0
% 3.24/0.98  
%------------------------------------------------------------------------------
