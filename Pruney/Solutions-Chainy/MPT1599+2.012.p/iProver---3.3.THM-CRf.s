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
% DateTime   : Thu Dec  3 12:20:09 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :  204 (1811 expanded)
%              Number of clauses        :  141 ( 634 expanded)
%              Number of leaves         :   16 ( 477 expanded)
%              Depth                    :   22
%              Number of atoms          :  715 (6671 expanded)
%              Number of equality atoms :  265 (1142 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v2_lattice3(k2_yellow_1(X0))
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
               => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( v2_lattice3(k2_yellow_1(X0))
         => ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
          & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
     => ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,sK2),k3_xboole_0(X1,sK2))
        & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
     => ( ? [X2] :
            ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),sK1,X2),k3_xboole_0(sK1,X2))
            & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
        & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
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
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) )
      & v2_lattice3(k2_yellow_1(sK0))
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))
    & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    & v2_lattice3(k2_yellow_1(sK0))
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f38,f37,f36])).

fof(f59,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f66,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k12_lattice3(X0,X1,X2) = X1
              <=> r3_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k12_lattice3(X0,X1,X2) = X1
              <=> r3_orders_2(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k12_lattice3(X0,X1,X2) = X1
              <=> r3_orders_2(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k12_lattice3(X0,X1,X2) = X1
                  | ~ r3_orders_2(X0,X1,X2) )
                & ( r3_orders_2(X0,X1,X2)
                  | k12_lattice3(X0,X1,X2) != X1 ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = X1
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f52,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f54,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f51,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f60,plain,(
    v2_lattice3(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f62,plain,(
    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
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
                 => ( v4_orders_2(X0)
                   => k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) = k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) = k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3)
                  | ~ v4_orders_2(X0)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) = k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3)
                  | ~ v4_orders_2(X0)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) = k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3)
      | ~ v4_orders_2(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f53,plain,(
    ! [X0] : v4_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | k12_lattice3(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f63,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f39])).

fof(f65,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k1_setfam_1(k2_tarski(sK1,sK2))) ),
    inference(definition_unfolding,[],[f63,f44])).

cnf(c_16,plain,
    ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | r1_tarski(X1,X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_21,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_268,plain,
    ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | r1_tarski(X1,X2)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_269,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK0),X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
    | r1_tarski(X0,X1) ),
    inference(unflattening,[status(thm)],[c_268])).

cnf(c_3735,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK0),X0,sK1)
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | r1_tarski(X0,sK1) ),
    inference(instantiation,[status(thm)],[c_269])).

cnf(c_9051,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_3735])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1226,plain,
    ( m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_14,plain,
    ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1238,plain,
    ( m1_subset_1(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1226,c_14])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1230,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_15,plain,
    ( r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ r1_tarski(X1,X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_284,plain,
    ( r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ r1_tarski(X1,X2)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_21])).

cnf(c_285,plain,
    ( r3_orders_2(k2_yellow_1(sK0),X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ r1_tarski(X0,X1) ),
    inference(unflattening,[status(thm)],[c_284])).

cnf(c_1222,plain,
    ( r3_orders_2(k2_yellow_1(sK0),X0,X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_285])).

cnf(c_1265,plain,
    ( r3_orders_2(k2_yellow_1(sK0),X0,X1) = iProver_top
    | m1_subset_1(X0,sK0) != iProver_top
    | m1_subset_1(X1,sK0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1222,c_14])).

cnf(c_8,plain,
    ( ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k12_lattice3(X0,X1,X2) = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_13,plain,
    ( v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_339,plain,
    ( ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k12_lattice3(X0,X1,X2) = X1
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_13])).

cnf(c_340,plain,
    ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ v5_orders_2(k2_yellow_1(X0))
    | ~ v2_lattice3(k2_yellow_1(X0))
    | ~ l1_orders_2(k2_yellow_1(X0))
    | k12_lattice3(k2_yellow_1(X0),X1,X2) = X1 ),
    inference(unflattening,[status(thm)],[c_339])).

cnf(c_11,plain,
    ( v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_10,plain,
    ( l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_344,plain,
    ( ~ v2_lattice3(k2_yellow_1(X0))
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | k12_lattice3(k2_yellow_1(X0),X1,X2) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_340,c_11,c_10])).

cnf(c_345,plain,
    ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ v2_lattice3(k2_yellow_1(X0))
    | k12_lattice3(k2_yellow_1(X0),X1,X2) = X1 ),
    inference(renaming,[status(thm)],[c_344])).

cnf(c_1220,plain,
    ( k12_lattice3(k2_yellow_1(X0),X1,X2) = X1
    | r3_orders_2(k2_yellow_1(X0),X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | v2_lattice3(k2_yellow_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_345])).

cnf(c_1301,plain,
    ( k12_lattice3(k2_yellow_1(X0),X1,X2) = X1
    | r3_orders_2(k2_yellow_1(X0),X1,X2) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | v2_lattice3(k2_yellow_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1220,c_14])).

cnf(c_3210,plain,
    ( k12_lattice3(k2_yellow_1(sK0),X0,X1) = X0
    | m1_subset_1(X0,sK0) != iProver_top
    | m1_subset_1(X1,sK0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v2_lattice3(k2_yellow_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1265,c_1301])).

cnf(c_20,negated_conjecture,
    ( v2_lattice3(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_23,plain,
    ( v2_lattice3(k2_yellow_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7361,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X1,sK0) != iProver_top
    | m1_subset_1(X0,sK0) != iProver_top
    | k12_lattice3(k2_yellow_1(sK0),X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3210,c_23])).

cnf(c_7362,plain,
    ( k12_lattice3(k2_yellow_1(sK0),X0,X1) = X0
    | m1_subset_1(X0,sK0) != iProver_top
    | m1_subset_1(X1,sK0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_7361])).

cnf(c_7371,plain,
    ( k12_lattice3(k2_yellow_1(sK0),X0,X0) = X0
    | m1_subset_1(X0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1230,c_7362])).

cnf(c_7396,plain,
    ( k12_lattice3(k2_yellow_1(sK0),sK1,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_1238,c_7371])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_401,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0)
    | k2_yellow_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_11])).

cnf(c_402,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | ~ v2_lattice3(k2_yellow_1(X1))
    | ~ l1_orders_2(k2_yellow_1(X1))
    | k12_lattice3(k2_yellow_1(X1),X0,X2) = k11_lattice3(k2_yellow_1(X1),X0,X2) ),
    inference(unflattening,[status(thm)],[c_401])).

cnf(c_416,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | ~ v2_lattice3(k2_yellow_1(X1))
    | k12_lattice3(k2_yellow_1(X1),X0,X2) = k11_lattice3(k2_yellow_1(X1),X0,X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_402,c_10])).

cnf(c_1218,plain,
    ( k12_lattice3(k2_yellow_1(X0),X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2)
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | v2_lattice3(k2_yellow_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_416])).

cnf(c_1283,plain,
    ( k12_lattice3(k2_yellow_1(X0),X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2)
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | v2_lattice3(k2_yellow_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1218,c_14])).

cnf(c_2030,plain,
    ( k12_lattice3(k2_yellow_1(sK0),sK1,X0) = k11_lattice3(k2_yellow_1(sK0),sK1,X0)
    | m1_subset_1(X0,sK0) != iProver_top
    | v2_lattice3(k2_yellow_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1238,c_1283])).

cnf(c_2566,plain,
    ( m1_subset_1(X0,sK0) != iProver_top
    | k12_lattice3(k2_yellow_1(sK0),sK1,X0) = k11_lattice3(k2_yellow_1(sK0),sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2030,c_23])).

cnf(c_2567,plain,
    ( k12_lattice3(k2_yellow_1(sK0),sK1,X0) = k11_lattice3(k2_yellow_1(sK0),sK1,X0)
    | m1_subset_1(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2566])).

cnf(c_2574,plain,
    ( k12_lattice3(k2_yellow_1(sK0),sK1,sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,sK1) ),
    inference(superposition,[status(thm)],[c_1238,c_2567])).

cnf(c_7523,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_7396,c_2574])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1227,plain,
    ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1241,plain,
    ( m1_subset_1(sK2,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1227,c_14])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,k11_lattice3(X1,X2,X0),X3) = k11_lattice3(X1,X2,k11_lattice3(X1,X0,X3)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_12,plain,
    ( v4_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_234,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,X2,k11_lattice3(X1,X0,X3)) = k11_lattice3(X1,k11_lattice3(X1,X2,X0),X3)
    | k2_yellow_1(X4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_12])).

cnf(c_235,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
    | ~ v5_orders_2(k2_yellow_1(X1))
    | ~ v2_lattice3(k2_yellow_1(X1))
    | ~ l1_orders_2(k2_yellow_1(X1))
    | k11_lattice3(k2_yellow_1(X1),X2,k11_lattice3(k2_yellow_1(X1),X3,X0)) = k11_lattice3(k2_yellow_1(X1),k11_lattice3(k2_yellow_1(X1),X2,X3),X0) ),
    inference(unflattening,[status(thm)],[c_234])).

cnf(c_253,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
    | ~ v2_lattice3(k2_yellow_1(X1))
    | k11_lattice3(k2_yellow_1(X1),X2,k11_lattice3(k2_yellow_1(X1),X3,X0)) = k11_lattice3(k2_yellow_1(X1),k11_lattice3(k2_yellow_1(X1),X2,X3),X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_235,c_10,c_11])).

cnf(c_1224,plain,
    ( k11_lattice3(k2_yellow_1(X0),X1,k11_lattice3(k2_yellow_1(X0),X2,X3)) = k11_lattice3(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X3)
    | m1_subset_1(X3,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | v2_lattice3(k2_yellow_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_253])).

cnf(c_1323,plain,
    ( k11_lattice3(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X3) = k11_lattice3(k2_yellow_1(X0),X1,k11_lattice3(k2_yellow_1(X0),X2,X3))
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | v2_lattice3(k2_yellow_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1224,c_14])).

cnf(c_3305,plain,
    ( k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,X0),X1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),X0,X1))
    | m1_subset_1(X0,sK0) != iProver_top
    | m1_subset_1(X1,sK0) != iProver_top
    | v2_lattice3(k2_yellow_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1238,c_1323])).

cnf(c_4438,plain,
    ( m1_subset_1(X1,sK0) != iProver_top
    | m1_subset_1(X0,sK0) != iProver_top
    | k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,X0),X1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3305,c_23])).

cnf(c_4439,plain,
    ( k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,X0),X1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),X0,X1))
    | m1_subset_1(X0,sK0) != iProver_top
    | m1_subset_1(X1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4438])).

cnf(c_4447,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,X0)) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK1),X0)
    | m1_subset_1(X0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1238,c_4439])).

cnf(c_4499,plain,
    ( k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK1),sK2) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1241,c_4447])).

cnf(c_7689,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) = k11_lattice3(k2_yellow_1(sK0),sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_7523,c_4499])).

cnf(c_2031,plain,
    ( k12_lattice3(k2_yellow_1(sK0),sK2,X0) = k11_lattice3(k2_yellow_1(sK0),sK2,X0)
    | m1_subset_1(X0,sK0) != iProver_top
    | v2_lattice3(k2_yellow_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1241,c_1283])).

cnf(c_2733,plain,
    ( m1_subset_1(X0,sK0) != iProver_top
    | k12_lattice3(k2_yellow_1(sK0),sK2,X0) = k11_lattice3(k2_yellow_1(sK0),sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2031,c_23])).

cnf(c_2734,plain,
    ( k12_lattice3(k2_yellow_1(sK0),sK2,X0) = k11_lattice3(k2_yellow_1(sK0),sK2,X0)
    | m1_subset_1(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2733])).

cnf(c_2742,plain,
    ( k12_lattice3(k2_yellow_1(sK0),sK2,sK2) = k11_lattice3(k2_yellow_1(sK0),sK2,sK2) ),
    inference(superposition,[status(thm)],[c_1241,c_2734])).

cnf(c_9,plain,
    ( r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k12_lattice3(X0,X1,X2) != X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_312,plain,
    ( r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k12_lattice3(X0,X1,X2) != X1
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_13])).

cnf(c_313,plain,
    ( r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ v5_orders_2(k2_yellow_1(X0))
    | ~ v2_lattice3(k2_yellow_1(X0))
    | ~ l1_orders_2(k2_yellow_1(X0))
    | k12_lattice3(k2_yellow_1(X0),X1,X2) != X1 ),
    inference(unflattening,[status(thm)],[c_312])).

cnf(c_317,plain,
    ( ~ v2_lattice3(k2_yellow_1(X0))
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | k12_lattice3(k2_yellow_1(X0),X1,X2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_313,c_11,c_10])).

cnf(c_318,plain,
    ( r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ v2_lattice3(k2_yellow_1(X0))
    | k12_lattice3(k2_yellow_1(X0),X1,X2) != X1 ),
    inference(renaming,[status(thm)],[c_317])).

cnf(c_1221,plain,
    ( k12_lattice3(k2_yellow_1(X0),X1,X2) != X1
    | r3_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | v2_lattice3(k2_yellow_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_318])).

cnf(c_1312,plain,
    ( k12_lattice3(k2_yellow_1(X0),X1,X2) != X1
    | r3_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | v2_lattice3(k2_yellow_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1221,c_14])).

cnf(c_3255,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK2,sK2) != sK2
    | r3_orders_2(k2_yellow_1(sK0),sK2,sK2) = iProver_top
    | m1_subset_1(sK2,sK0) != iProver_top
    | v2_lattice3(k2_yellow_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2742,c_1312])).

cnf(c_25,plain,
    ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1385,plain,
    ( r3_orders_2(k2_yellow_1(sK0),sK2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ r1_tarski(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_285])).

cnf(c_1638,plain,
    ( r3_orders_2(k2_yellow_1(sK0),sK2,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1385])).

cnf(c_1640,plain,
    ( r3_orders_2(k2_yellow_1(sK0),sK2,sK2) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) != iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1638])).

cnf(c_1639,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1642,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1639])).

cnf(c_4962,plain,
    ( r3_orders_2(k2_yellow_1(sK0),sK2,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3255,c_25,c_1640,c_1642])).

cnf(c_4967,plain,
    ( k12_lattice3(k2_yellow_1(sK0),sK2,sK2) = sK2
    | m1_subset_1(sK2,sK0) != iProver_top
    | v2_lattice3(k2_yellow_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4962,c_1301])).

cnf(c_4974,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK2,sK2) = sK2
    | m1_subset_1(sK2,sK0) != iProver_top
    | v2_lattice3(k2_yellow_1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4967,c_2742])).

cnf(c_6240,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK2,sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4974,c_23,c_1241])).

cnf(c_3306,plain,
    ( k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK2,X0),X1) = k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),X0,X1))
    | m1_subset_1(X0,sK0) != iProver_top
    | m1_subset_1(X1,sK0) != iProver_top
    | v2_lattice3(k2_yellow_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1241,c_1323])).

cnf(c_4575,plain,
    ( m1_subset_1(X1,sK0) != iProver_top
    | m1_subset_1(X0,sK0) != iProver_top
    | k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK2,X0),X1) = k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3306,c_23])).

cnf(c_4576,plain,
    ( k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK2,X0),X1) = k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),X0,X1))
    | m1_subset_1(X0,sK0) != iProver_top
    | m1_subset_1(X1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4575])).

cnf(c_4585,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK2,X0)) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK2,sK2),X0)
    | m1_subset_1(X0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1241,c_4576])).

cnf(c_4793,plain,
    ( k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK2,sK2),sK1) = k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_1238,c_4585])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,X0,X2) = k11_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_378,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,X0,X2) = k11_lattice3(X1,X2,X0)
    | k2_yellow_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_11])).

cnf(c_379,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | ~ v2_lattice3(k2_yellow_1(X1))
    | ~ l1_orders_2(k2_yellow_1(X1))
    | k11_lattice3(k2_yellow_1(X1),X2,X0) = k11_lattice3(k2_yellow_1(X1),X0,X2) ),
    inference(unflattening,[status(thm)],[c_378])).

cnf(c_393,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | ~ v2_lattice3(k2_yellow_1(X1))
    | k11_lattice3(k2_yellow_1(X1),X2,X0) = k11_lattice3(k2_yellow_1(X1),X0,X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_379,c_10])).

cnf(c_1219,plain,
    ( k11_lattice3(k2_yellow_1(X0),X1,X2) = k11_lattice3(k2_yellow_1(X0),X2,X1)
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | v2_lattice3(k2_yellow_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_393])).

cnf(c_1292,plain,
    ( k11_lattice3(k2_yellow_1(X0),X1,X2) = k11_lattice3(k2_yellow_1(X0),X2,X1)
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | v2_lattice3(k2_yellow_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1219,c_14])).

cnf(c_3170,plain,
    ( k11_lattice3(k2_yellow_1(sK0),X0,sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,X0)
    | m1_subset_1(X0,sK0) != iProver_top
    | v2_lattice3(k2_yellow_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1238,c_1292])).

cnf(c_3614,plain,
    ( m1_subset_1(X0,sK0) != iProver_top
    | k11_lattice3(k2_yellow_1(sK0),X0,sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3170,c_23])).

cnf(c_3615,plain,
    ( k11_lattice3(k2_yellow_1(sK0),X0,sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,X0)
    | m1_subset_1(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3614])).

cnf(c_3623,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK2,sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1241,c_3615])).

cnf(c_4805,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK2,sK2),sK1) ),
    inference(light_normalisation,[status(thm)],[c_4793,c_3623])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_434,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
    | k2_yellow_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_10])).

cnf(c_435,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),u1_struct_0(k2_yellow_1(X1))) ),
    inference(unflattening,[status(thm)],[c_434])).

cnf(c_1217,plain,
    ( m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) != iProver_top
    | m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),u1_struct_0(k2_yellow_1(X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_435])).

cnf(c_1258,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,X1) != iProver_top
    | m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1217,c_14])).

cnf(c_4861,plain,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)),sK0) = iProver_top
    | m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK2,sK2),sK0) != iProver_top
    | m1_subset_1(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4805,c_1258])).

cnf(c_5731,plain,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK2,sK2),sK0) != iProver_top
    | m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4861,c_1238])).

cnf(c_5732,plain,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)),sK0) = iProver_top
    | m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK2,sK2),sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5731])).

cnf(c_4584,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,X0)) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK2,sK1),X0)
    | m1_subset_1(X0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1238,c_4576])).

cnf(c_4601,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,X0)) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),X0)
    | m1_subset_1(X0,sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4584,c_3623])).

cnf(c_4867,plain,
    ( k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) = k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1241,c_4601])).

cnf(c_4448,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK2,X0)) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),X0)
    | m1_subset_1(X0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1241,c_4439])).

cnf(c_4550,plain,
    ( k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK2,sK2)) ),
    inference(superposition,[status(thm)],[c_1241,c_4448])).

cnf(c_4876,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK2,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_4867,c_4550])).

cnf(c_5735,plain,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK2,sK2),sK0) != iProver_top
    | m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK2,sK2)),sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5732,c_4876])).

cnf(c_6247,plain,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) = iProver_top
    | m1_subset_1(sK2,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6240,c_5735])).

cnf(c_6275,plain,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6247])).

cnf(c_2032,plain,
    ( k12_lattice3(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X3) = k11_lattice3(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X3)
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | v2_lattice3(k2_yellow_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1258,c_1283])).

cnf(c_4921,plain,
    ( k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,X0),X1) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,X0),X1)
    | m1_subset_1(X0,sK0) != iProver_top
    | m1_subset_1(X1,sK0) != iProver_top
    | v2_lattice3(k2_yellow_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1238,c_2032])).

cnf(c_5306,plain,
    ( m1_subset_1(X1,sK0) != iProver_top
    | m1_subset_1(X0,sK0) != iProver_top
    | k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,X0),X1) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4921,c_23])).

cnf(c_5307,plain,
    ( k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,X0),X1) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,X0),X1)
    | m1_subset_1(X0,sK0) != iProver_top
    | m1_subset_1(X1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5306])).

cnf(c_5316,plain,
    ( k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),X0) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),X0)
    | m1_subset_1(X0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1241,c_5307])).

cnf(c_5406,plain,
    ( k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) ),
    inference(superposition,[status(thm)],[c_1241,c_5316])).

cnf(c_5425,plain,
    ( k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK2,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_5406,c_4550])).

cnf(c_6246,plain,
    ( k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) = k11_lattice3(k2_yellow_1(sK0),sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_6240,c_5425])).

cnf(c_5405,plain,
    ( k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
    inference(superposition,[status(thm)],[c_1238,c_5316])).

cnf(c_4549,plain,
    ( k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_1238,c_4448])).

cnf(c_4561,plain,
    ( k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_4549,c_3623])).

cnf(c_5428,plain,
    ( k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_5405,c_4561])).

cnf(c_6113,plain,
    ( k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) != k11_lattice3(k2_yellow_1(sK0),sK1,sK2)
    | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) = iProver_top
    | m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) != iProver_top
    | m1_subset_1(sK1,sK0) != iProver_top
    | v2_lattice3(k2_yellow_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5428,c_1312])).

cnf(c_6114,plain,
    ( r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | ~ m1_subset_1(sK1,sK0)
    | ~ v2_lattice3(k2_yellow_1(sK0))
    | k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) != k11_lattice3(k2_yellow_1(sK0),sK1,sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6113])).

cnf(c_1456,plain,
    ( r3_orders_2(k2_yellow_1(sK0),X0,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ v2_lattice3(k2_yellow_1(sK0))
    | k12_lattice3(k2_yellow_1(sK0),X0,sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_318])).

cnf(c_1991,plain,
    ( r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ v2_lattice3(k2_yellow_1(sK0))
    | k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) != k11_lattice3(k2_yellow_1(sK0),sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1456])).

cnf(c_1412,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
    | m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,X0),u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_435])).

cnf(c_1621,plain,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_1412])).

cnf(c_1498,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_269])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1404,plain,
    ( r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k1_setfam_1(k2_tarski(sK1,sK2)))
    | ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
    | ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1354,plain,
    ( m1_subset_1(sK2,sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1241])).

cnf(c_1353,plain,
    ( m1_subset_1(sK1,sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1238])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k1_setfam_1(k2_tarski(sK1,sK2))) ),
    inference(cnf_transformation,[],[f65])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9051,c_7689,c_6275,c_6246,c_6114,c_1991,c_1621,c_1498,c_1404,c_1354,c_1353,c_17,c_18,c_19,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:45:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.61/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.61/0.98  
% 3.61/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.61/0.98  
% 3.61/0.98  ------  iProver source info
% 3.61/0.98  
% 3.61/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.61/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.61/0.98  git: non_committed_changes: false
% 3.61/0.98  git: last_make_outside_of_git: false
% 3.61/0.98  
% 3.61/0.98  ------ 
% 3.61/0.98  
% 3.61/0.98  ------ Input Options
% 3.61/0.98  
% 3.61/0.98  --out_options                           all
% 3.61/0.98  --tptp_safe_out                         true
% 3.61/0.98  --problem_path                          ""
% 3.61/0.98  --include_path                          ""
% 3.61/0.98  --clausifier                            res/vclausify_rel
% 3.61/0.98  --clausifier_options                    --mode clausify
% 3.61/0.98  --stdin                                 false
% 3.61/0.98  --stats_out                             all
% 3.61/0.98  
% 3.61/0.98  ------ General Options
% 3.61/0.98  
% 3.61/0.98  --fof                                   false
% 3.61/0.98  --time_out_real                         305.
% 3.61/0.98  --time_out_virtual                      -1.
% 3.61/0.98  --symbol_type_check                     false
% 3.61/0.98  --clausify_out                          false
% 3.61/0.98  --sig_cnt_out                           false
% 3.61/0.98  --trig_cnt_out                          false
% 3.61/0.98  --trig_cnt_out_tolerance                1.
% 3.61/0.98  --trig_cnt_out_sk_spl                   false
% 3.61/0.98  --abstr_cl_out                          false
% 3.61/0.98  
% 3.61/0.98  ------ Global Options
% 3.61/0.98  
% 3.61/0.98  --schedule                              default
% 3.61/0.98  --add_important_lit                     false
% 3.61/0.98  --prop_solver_per_cl                    1000
% 3.61/0.98  --min_unsat_core                        false
% 3.61/0.98  --soft_assumptions                      false
% 3.61/0.98  --soft_lemma_size                       3
% 3.61/0.98  --prop_impl_unit_size                   0
% 3.61/0.98  --prop_impl_unit                        []
% 3.61/0.98  --share_sel_clauses                     true
% 3.61/0.98  --reset_solvers                         false
% 3.61/0.98  --bc_imp_inh                            [conj_cone]
% 3.61/0.98  --conj_cone_tolerance                   3.
% 3.61/0.98  --extra_neg_conj                        none
% 3.61/0.98  --large_theory_mode                     true
% 3.61/0.98  --prolific_symb_bound                   200
% 3.61/0.98  --lt_threshold                          2000
% 3.61/0.98  --clause_weak_htbl                      true
% 3.61/0.98  --gc_record_bc_elim                     false
% 3.61/0.98  
% 3.61/0.98  ------ Preprocessing Options
% 3.61/0.98  
% 3.61/0.98  --preprocessing_flag                    true
% 3.61/0.98  --time_out_prep_mult                    0.1
% 3.61/0.98  --splitting_mode                        input
% 3.61/0.98  --splitting_grd                         true
% 3.61/0.98  --splitting_cvd                         false
% 3.61/0.98  --splitting_cvd_svl                     false
% 3.61/0.98  --splitting_nvd                         32
% 3.61/0.98  --sub_typing                            true
% 3.61/0.98  --prep_gs_sim                           true
% 3.61/0.98  --prep_unflatten                        true
% 3.61/0.98  --prep_res_sim                          true
% 3.61/0.98  --prep_upred                            true
% 3.61/0.98  --prep_sem_filter                       exhaustive
% 3.61/0.98  --prep_sem_filter_out                   false
% 3.61/0.98  --pred_elim                             true
% 3.61/0.98  --res_sim_input                         true
% 3.61/0.98  --eq_ax_congr_red                       true
% 3.61/0.98  --pure_diseq_elim                       true
% 3.61/0.98  --brand_transform                       false
% 3.61/0.98  --non_eq_to_eq                          false
% 3.61/0.98  --prep_def_merge                        true
% 3.61/0.98  --prep_def_merge_prop_impl              false
% 3.61/0.98  --prep_def_merge_mbd                    true
% 3.61/0.98  --prep_def_merge_tr_red                 false
% 3.61/0.98  --prep_def_merge_tr_cl                  false
% 3.61/0.98  --smt_preprocessing                     true
% 3.61/0.98  --smt_ac_axioms                         fast
% 3.61/0.98  --preprocessed_out                      false
% 3.61/0.98  --preprocessed_stats                    false
% 3.61/0.98  
% 3.61/0.98  ------ Abstraction refinement Options
% 3.61/0.98  
% 3.61/0.98  --abstr_ref                             []
% 3.61/0.98  --abstr_ref_prep                        false
% 3.61/0.98  --abstr_ref_until_sat                   false
% 3.61/0.98  --abstr_ref_sig_restrict                funpre
% 3.61/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.61/0.98  --abstr_ref_under                       []
% 3.61/0.98  
% 3.61/0.98  ------ SAT Options
% 3.61/0.98  
% 3.61/0.98  --sat_mode                              false
% 3.61/0.98  --sat_fm_restart_options                ""
% 3.61/0.98  --sat_gr_def                            false
% 3.61/0.98  --sat_epr_types                         true
% 3.61/0.98  --sat_non_cyclic_types                  false
% 3.61/0.98  --sat_finite_models                     false
% 3.61/0.98  --sat_fm_lemmas                         false
% 3.61/0.98  --sat_fm_prep                           false
% 3.61/0.98  --sat_fm_uc_incr                        true
% 3.61/0.98  --sat_out_model                         small
% 3.61/0.98  --sat_out_clauses                       false
% 3.61/0.98  
% 3.61/0.98  ------ QBF Options
% 3.61/0.98  
% 3.61/0.98  --qbf_mode                              false
% 3.61/0.98  --qbf_elim_univ                         false
% 3.61/0.98  --qbf_dom_inst                          none
% 3.61/0.98  --qbf_dom_pre_inst                      false
% 3.61/0.98  --qbf_sk_in                             false
% 3.61/0.98  --qbf_pred_elim                         true
% 3.61/0.98  --qbf_split                             512
% 3.61/0.98  
% 3.61/0.98  ------ BMC1 Options
% 3.61/0.98  
% 3.61/0.98  --bmc1_incremental                      false
% 3.61/0.98  --bmc1_axioms                           reachable_all
% 3.61/0.98  --bmc1_min_bound                        0
% 3.61/0.98  --bmc1_max_bound                        -1
% 3.61/0.98  --bmc1_max_bound_default                -1
% 3.61/0.98  --bmc1_symbol_reachability              true
% 3.61/0.98  --bmc1_property_lemmas                  false
% 3.61/0.98  --bmc1_k_induction                      false
% 3.61/0.98  --bmc1_non_equiv_states                 false
% 3.61/0.98  --bmc1_deadlock                         false
% 3.61/0.98  --bmc1_ucm                              false
% 3.61/0.98  --bmc1_add_unsat_core                   none
% 3.61/0.98  --bmc1_unsat_core_children              false
% 3.61/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.61/0.98  --bmc1_out_stat                         full
% 3.61/0.98  --bmc1_ground_init                      false
% 3.61/0.98  --bmc1_pre_inst_next_state              false
% 3.61/0.98  --bmc1_pre_inst_state                   false
% 3.61/0.98  --bmc1_pre_inst_reach_state             false
% 3.61/0.98  --bmc1_out_unsat_core                   false
% 3.61/0.98  --bmc1_aig_witness_out                  false
% 3.61/0.98  --bmc1_verbose                          false
% 3.61/0.98  --bmc1_dump_clauses_tptp                false
% 3.61/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.61/0.98  --bmc1_dump_file                        -
% 3.61/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.61/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.61/0.98  --bmc1_ucm_extend_mode                  1
% 3.61/0.98  --bmc1_ucm_init_mode                    2
% 3.61/0.98  --bmc1_ucm_cone_mode                    none
% 3.61/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.61/0.98  --bmc1_ucm_relax_model                  4
% 3.61/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.61/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.61/0.98  --bmc1_ucm_layered_model                none
% 3.61/0.98  --bmc1_ucm_max_lemma_size               10
% 3.61/0.98  
% 3.61/0.98  ------ AIG Options
% 3.61/0.98  
% 3.61/0.98  --aig_mode                              false
% 3.61/0.98  
% 3.61/0.98  ------ Instantiation Options
% 3.61/0.98  
% 3.61/0.98  --instantiation_flag                    true
% 3.61/0.98  --inst_sos_flag                         false
% 3.61/0.98  --inst_sos_phase                        true
% 3.61/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.61/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.61/0.98  --inst_lit_sel_side                     num_symb
% 3.61/0.98  --inst_solver_per_active                1400
% 3.61/0.98  --inst_solver_calls_frac                1.
% 3.61/0.98  --inst_passive_queue_type               priority_queues
% 3.61/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.61/0.98  --inst_passive_queues_freq              [25;2]
% 3.61/0.98  --inst_dismatching                      true
% 3.61/0.98  --inst_eager_unprocessed_to_passive     true
% 3.61/0.98  --inst_prop_sim_given                   true
% 3.61/0.98  --inst_prop_sim_new                     false
% 3.61/0.98  --inst_subs_new                         false
% 3.61/0.98  --inst_eq_res_simp                      false
% 3.61/0.98  --inst_subs_given                       false
% 3.61/0.98  --inst_orphan_elimination               true
% 3.61/0.98  --inst_learning_loop_flag               true
% 3.61/0.98  --inst_learning_start                   3000
% 3.61/0.98  --inst_learning_factor                  2
% 3.61/0.98  --inst_start_prop_sim_after_learn       3
% 3.61/0.98  --inst_sel_renew                        solver
% 3.61/0.98  --inst_lit_activity_flag                true
% 3.61/0.98  --inst_restr_to_given                   false
% 3.61/0.98  --inst_activity_threshold               500
% 3.61/0.98  --inst_out_proof                        true
% 3.61/0.98  
% 3.61/0.98  ------ Resolution Options
% 3.61/0.98  
% 3.61/0.98  --resolution_flag                       true
% 3.61/0.98  --res_lit_sel                           adaptive
% 3.61/0.98  --res_lit_sel_side                      none
% 3.61/0.98  --res_ordering                          kbo
% 3.61/0.98  --res_to_prop_solver                    active
% 3.61/0.98  --res_prop_simpl_new                    false
% 3.61/0.98  --res_prop_simpl_given                  true
% 3.61/0.98  --res_passive_queue_type                priority_queues
% 3.61/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.61/0.98  --res_passive_queues_freq               [15;5]
% 3.61/0.98  --res_forward_subs                      full
% 3.61/0.98  --res_backward_subs                     full
% 3.61/0.98  --res_forward_subs_resolution           true
% 3.61/0.98  --res_backward_subs_resolution          true
% 3.61/0.98  --res_orphan_elimination                true
% 3.61/0.98  --res_time_limit                        2.
% 3.61/0.98  --res_out_proof                         true
% 3.61/0.98  
% 3.61/0.98  ------ Superposition Options
% 3.61/0.98  
% 3.61/0.98  --superposition_flag                    true
% 3.61/0.98  --sup_passive_queue_type                priority_queues
% 3.61/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.61/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.61/0.98  --demod_completeness_check              fast
% 3.61/0.98  --demod_use_ground                      true
% 3.61/0.98  --sup_to_prop_solver                    passive
% 3.61/0.98  --sup_prop_simpl_new                    true
% 3.61/0.98  --sup_prop_simpl_given                  true
% 3.61/0.98  --sup_fun_splitting                     false
% 3.61/0.98  --sup_smt_interval                      50000
% 3.61/0.98  
% 3.61/0.98  ------ Superposition Simplification Setup
% 3.61/0.98  
% 3.61/0.98  --sup_indices_passive                   []
% 3.61/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.61/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.61/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.61/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.61/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.61/0.98  --sup_full_bw                           [BwDemod]
% 3.61/0.98  --sup_immed_triv                        [TrivRules]
% 3.61/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.61/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.61/0.98  --sup_immed_bw_main                     []
% 3.61/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.61/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.61/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.61/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.61/0.98  
% 3.61/0.98  ------ Combination Options
% 3.61/0.98  
% 3.61/0.98  --comb_res_mult                         3
% 3.61/0.98  --comb_sup_mult                         2
% 3.61/0.98  --comb_inst_mult                        10
% 3.61/0.98  
% 3.61/0.98  ------ Debug Options
% 3.61/0.98  
% 3.61/0.98  --dbg_backtrace                         false
% 3.61/0.98  --dbg_dump_prop_clauses                 false
% 3.61/0.98  --dbg_dump_prop_clauses_file            -
% 3.61/0.98  --dbg_out_stat                          false
% 3.61/0.98  ------ Parsing...
% 3.61/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.61/0.98  
% 3.61/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.61/0.98  
% 3.61/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.61/0.98  
% 3.61/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.61/0.98  ------ Proving...
% 3.61/0.98  ------ Problem Properties 
% 3.61/0.98  
% 3.61/0.98  
% 3.61/0.98  clauses                                 16
% 3.61/0.98  conjectures                             4
% 3.61/0.98  EPR                                     2
% 3.61/0.98  Horn                                    16
% 3.61/0.98  unary                                   6
% 3.61/0.98  binary                                  0
% 3.61/0.98  lits                                    46
% 3.61/0.98  lits eq                                 7
% 3.61/0.98  fd_pure                                 0
% 3.61/0.98  fd_pseudo                               0
% 3.61/0.98  fd_cond                                 0
% 3.61/0.98  fd_pseudo_cond                          1
% 3.61/0.98  AC symbols                              0
% 3.61/0.98  
% 3.61/0.98  ------ Schedule dynamic 5 is on 
% 3.61/0.98  
% 3.61/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.61/0.98  
% 3.61/0.98  
% 3.61/0.98  ------ 
% 3.61/0.98  Current options:
% 3.61/0.98  ------ 
% 3.61/0.98  
% 3.61/0.98  ------ Input Options
% 3.61/0.98  
% 3.61/0.98  --out_options                           all
% 3.61/0.98  --tptp_safe_out                         true
% 3.61/0.98  --problem_path                          ""
% 3.61/0.98  --include_path                          ""
% 3.61/0.98  --clausifier                            res/vclausify_rel
% 3.61/0.98  --clausifier_options                    --mode clausify
% 3.61/0.98  --stdin                                 false
% 3.61/0.98  --stats_out                             all
% 3.61/0.98  
% 3.61/0.98  ------ General Options
% 3.61/0.98  
% 3.61/0.98  --fof                                   false
% 3.61/0.98  --time_out_real                         305.
% 3.61/0.98  --time_out_virtual                      -1.
% 3.61/0.98  --symbol_type_check                     false
% 3.61/0.98  --clausify_out                          false
% 3.61/0.98  --sig_cnt_out                           false
% 3.61/0.98  --trig_cnt_out                          false
% 3.61/0.98  --trig_cnt_out_tolerance                1.
% 3.61/0.98  --trig_cnt_out_sk_spl                   false
% 3.61/0.98  --abstr_cl_out                          false
% 3.61/0.98  
% 3.61/0.98  ------ Global Options
% 3.61/0.98  
% 3.61/0.98  --schedule                              default
% 3.61/0.98  --add_important_lit                     false
% 3.61/0.98  --prop_solver_per_cl                    1000
% 3.61/0.98  --min_unsat_core                        false
% 3.61/0.98  --soft_assumptions                      false
% 3.61/0.98  --soft_lemma_size                       3
% 3.61/0.98  --prop_impl_unit_size                   0
% 3.61/0.98  --prop_impl_unit                        []
% 3.61/0.98  --share_sel_clauses                     true
% 3.61/0.98  --reset_solvers                         false
% 3.61/0.98  --bc_imp_inh                            [conj_cone]
% 3.61/0.98  --conj_cone_tolerance                   3.
% 3.61/0.98  --extra_neg_conj                        none
% 3.61/0.98  --large_theory_mode                     true
% 3.61/0.98  --prolific_symb_bound                   200
% 3.61/0.98  --lt_threshold                          2000
% 3.61/0.98  --clause_weak_htbl                      true
% 3.61/0.98  --gc_record_bc_elim                     false
% 3.61/0.98  
% 3.61/0.98  ------ Preprocessing Options
% 3.61/0.98  
% 3.61/0.98  --preprocessing_flag                    true
% 3.61/0.98  --time_out_prep_mult                    0.1
% 3.61/0.98  --splitting_mode                        input
% 3.61/0.98  --splitting_grd                         true
% 3.61/0.98  --splitting_cvd                         false
% 3.61/0.98  --splitting_cvd_svl                     false
% 3.61/0.98  --splitting_nvd                         32
% 3.61/0.98  --sub_typing                            true
% 3.61/0.98  --prep_gs_sim                           true
% 3.61/0.98  --prep_unflatten                        true
% 3.61/0.98  --prep_res_sim                          true
% 3.61/0.98  --prep_upred                            true
% 3.61/0.98  --prep_sem_filter                       exhaustive
% 3.61/0.98  --prep_sem_filter_out                   false
% 3.61/0.98  --pred_elim                             true
% 3.61/0.98  --res_sim_input                         true
% 3.61/0.98  --eq_ax_congr_red                       true
% 3.61/0.98  --pure_diseq_elim                       true
% 3.61/0.98  --brand_transform                       false
% 3.61/0.98  --non_eq_to_eq                          false
% 3.61/0.98  --prep_def_merge                        true
% 3.61/0.98  --prep_def_merge_prop_impl              false
% 3.61/0.98  --prep_def_merge_mbd                    true
% 3.61/0.98  --prep_def_merge_tr_red                 false
% 3.61/0.98  --prep_def_merge_tr_cl                  false
% 3.61/0.98  --smt_preprocessing                     true
% 3.61/0.98  --smt_ac_axioms                         fast
% 3.61/0.98  --preprocessed_out                      false
% 3.61/0.98  --preprocessed_stats                    false
% 3.61/0.98  
% 3.61/0.98  ------ Abstraction refinement Options
% 3.61/0.98  
% 3.61/0.98  --abstr_ref                             []
% 3.61/0.98  --abstr_ref_prep                        false
% 3.61/0.98  --abstr_ref_until_sat                   false
% 3.61/0.98  --abstr_ref_sig_restrict                funpre
% 3.61/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.61/0.98  --abstr_ref_under                       []
% 3.61/0.98  
% 3.61/0.98  ------ SAT Options
% 3.61/0.98  
% 3.61/0.98  --sat_mode                              false
% 3.61/0.98  --sat_fm_restart_options                ""
% 3.61/0.98  --sat_gr_def                            false
% 3.61/0.98  --sat_epr_types                         true
% 3.61/0.98  --sat_non_cyclic_types                  false
% 3.61/0.98  --sat_finite_models                     false
% 3.61/0.98  --sat_fm_lemmas                         false
% 3.61/0.98  --sat_fm_prep                           false
% 3.61/0.98  --sat_fm_uc_incr                        true
% 3.61/0.98  --sat_out_model                         small
% 3.61/0.98  --sat_out_clauses                       false
% 3.61/0.98  
% 3.61/0.98  ------ QBF Options
% 3.61/0.98  
% 3.61/0.98  --qbf_mode                              false
% 3.61/0.98  --qbf_elim_univ                         false
% 3.61/0.98  --qbf_dom_inst                          none
% 3.61/0.98  --qbf_dom_pre_inst                      false
% 3.61/0.98  --qbf_sk_in                             false
% 3.61/0.98  --qbf_pred_elim                         true
% 3.61/0.98  --qbf_split                             512
% 3.61/0.98  
% 3.61/0.98  ------ BMC1 Options
% 3.61/0.98  
% 3.61/0.98  --bmc1_incremental                      false
% 3.61/0.98  --bmc1_axioms                           reachable_all
% 3.61/0.98  --bmc1_min_bound                        0
% 3.61/0.98  --bmc1_max_bound                        -1
% 3.61/0.98  --bmc1_max_bound_default                -1
% 3.61/0.98  --bmc1_symbol_reachability              true
% 3.61/0.98  --bmc1_property_lemmas                  false
% 3.61/0.98  --bmc1_k_induction                      false
% 3.61/0.98  --bmc1_non_equiv_states                 false
% 3.61/0.98  --bmc1_deadlock                         false
% 3.61/0.98  --bmc1_ucm                              false
% 3.61/0.98  --bmc1_add_unsat_core                   none
% 3.61/0.98  --bmc1_unsat_core_children              false
% 3.61/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.61/0.98  --bmc1_out_stat                         full
% 3.61/0.98  --bmc1_ground_init                      false
% 3.61/0.98  --bmc1_pre_inst_next_state              false
% 3.61/0.98  --bmc1_pre_inst_state                   false
% 3.61/0.98  --bmc1_pre_inst_reach_state             false
% 3.61/0.98  --bmc1_out_unsat_core                   false
% 3.61/0.98  --bmc1_aig_witness_out                  false
% 3.61/0.98  --bmc1_verbose                          false
% 3.61/0.98  --bmc1_dump_clauses_tptp                false
% 3.61/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.61/0.98  --bmc1_dump_file                        -
% 3.61/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.61/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.61/0.98  --bmc1_ucm_extend_mode                  1
% 3.61/0.98  --bmc1_ucm_init_mode                    2
% 3.61/0.98  --bmc1_ucm_cone_mode                    none
% 3.61/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.61/0.98  --bmc1_ucm_relax_model                  4
% 3.61/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.61/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.61/0.98  --bmc1_ucm_layered_model                none
% 3.61/0.98  --bmc1_ucm_max_lemma_size               10
% 3.61/0.98  
% 3.61/0.98  ------ AIG Options
% 3.61/0.98  
% 3.61/0.98  --aig_mode                              false
% 3.61/0.98  
% 3.61/0.98  ------ Instantiation Options
% 3.61/0.98  
% 3.61/0.98  --instantiation_flag                    true
% 3.61/0.98  --inst_sos_flag                         false
% 3.61/0.98  --inst_sos_phase                        true
% 3.61/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.61/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.61/0.98  --inst_lit_sel_side                     none
% 3.61/0.98  --inst_solver_per_active                1400
% 3.61/0.98  --inst_solver_calls_frac                1.
% 3.61/0.98  --inst_passive_queue_type               priority_queues
% 3.61/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.61/0.98  --inst_passive_queues_freq              [25;2]
% 3.61/0.98  --inst_dismatching                      true
% 3.61/0.98  --inst_eager_unprocessed_to_passive     true
% 3.61/0.98  --inst_prop_sim_given                   true
% 3.61/0.98  --inst_prop_sim_new                     false
% 3.61/0.98  --inst_subs_new                         false
% 3.61/0.98  --inst_eq_res_simp                      false
% 3.61/0.98  --inst_subs_given                       false
% 3.61/0.98  --inst_orphan_elimination               true
% 3.61/0.98  --inst_learning_loop_flag               true
% 3.61/0.98  --inst_learning_start                   3000
% 3.61/0.98  --inst_learning_factor                  2
% 3.61/0.98  --inst_start_prop_sim_after_learn       3
% 3.61/0.98  --inst_sel_renew                        solver
% 3.61/0.98  --inst_lit_activity_flag                true
% 3.61/0.98  --inst_restr_to_given                   false
% 3.61/0.98  --inst_activity_threshold               500
% 3.61/0.98  --inst_out_proof                        true
% 3.61/0.98  
% 3.61/0.98  ------ Resolution Options
% 3.61/0.98  
% 3.61/0.98  --resolution_flag                       false
% 3.61/0.98  --res_lit_sel                           adaptive
% 3.61/0.98  --res_lit_sel_side                      none
% 3.61/0.98  --res_ordering                          kbo
% 3.61/0.98  --res_to_prop_solver                    active
% 3.61/0.98  --res_prop_simpl_new                    false
% 3.61/0.98  --res_prop_simpl_given                  true
% 3.61/0.98  --res_passive_queue_type                priority_queues
% 3.61/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.61/0.98  --res_passive_queues_freq               [15;5]
% 3.61/0.98  --res_forward_subs                      full
% 3.61/0.98  --res_backward_subs                     full
% 3.61/0.98  --res_forward_subs_resolution           true
% 3.61/0.98  --res_backward_subs_resolution          true
% 3.61/0.98  --res_orphan_elimination                true
% 3.61/0.98  --res_time_limit                        2.
% 3.61/0.98  --res_out_proof                         true
% 3.61/0.98  
% 3.61/0.98  ------ Superposition Options
% 3.61/0.98  
% 3.61/0.98  --superposition_flag                    true
% 3.61/0.98  --sup_passive_queue_type                priority_queues
% 3.61/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.61/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.61/0.98  --demod_completeness_check              fast
% 3.61/0.98  --demod_use_ground                      true
% 3.61/0.98  --sup_to_prop_solver                    passive
% 3.61/0.98  --sup_prop_simpl_new                    true
% 3.61/0.98  --sup_prop_simpl_given                  true
% 3.61/0.98  --sup_fun_splitting                     false
% 3.61/0.98  --sup_smt_interval                      50000
% 3.61/0.98  
% 3.61/0.98  ------ Superposition Simplification Setup
% 3.61/0.98  
% 3.61/0.98  --sup_indices_passive                   []
% 3.61/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.61/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.61/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.61/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.61/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.61/0.98  --sup_full_bw                           [BwDemod]
% 3.61/0.98  --sup_immed_triv                        [TrivRules]
% 3.61/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.61/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.61/0.98  --sup_immed_bw_main                     []
% 3.61/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.61/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.61/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.61/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.61/0.98  
% 3.61/0.98  ------ Combination Options
% 3.61/0.98  
% 3.61/0.98  --comb_res_mult                         3
% 3.61/0.98  --comb_sup_mult                         2
% 3.61/0.98  --comb_inst_mult                        10
% 3.61/0.98  
% 3.61/0.98  ------ Debug Options
% 3.61/0.98  
% 3.61/0.98  --dbg_backtrace                         false
% 3.61/0.98  --dbg_dump_prop_clauses                 false
% 3.61/0.98  --dbg_dump_prop_clauses_file            -
% 3.61/0.98  --dbg_out_stat                          false
% 3.61/0.98  
% 3.61/0.98  
% 3.61/0.98  
% 3.61/0.98  
% 3.61/0.98  ------ Proving...
% 3.61/0.98  
% 3.61/0.98  
% 3.61/0.98  % SZS status Theorem for theBenchmark.p
% 3.61/0.98  
% 3.61/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.61/0.98  
% 3.61/0.98  fof(f12,axiom,(
% 3.61/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f29,plain,(
% 3.61/0.98    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 3.61/0.98    inference(ennf_transformation,[],[f12])).
% 3.61/0.98  
% 3.61/0.98  fof(f35,plain,(
% 3.61/0.98    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 3.61/0.98    inference(nnf_transformation,[],[f29])).
% 3.61/0.98  
% 3.61/0.98  fof(f57,plain,(
% 3.61/0.98    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f35])).
% 3.61/0.98  
% 3.61/0.98  fof(f13,conjecture,(
% 3.61/0.98    ! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f14,negated_conjecture,(
% 3.61/0.98    ~! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 3.61/0.98    inference(negated_conjecture,[],[f13])).
% 3.61/0.98  
% 3.61/0.98  fof(f30,plain,(
% 3.61/0.98    ? [X0] : ((? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0))) & ~v1_xboole_0(X0))),
% 3.61/0.98    inference(ennf_transformation,[],[f14])).
% 3.61/0.98  
% 3.61/0.98  fof(f31,plain,(
% 3.61/0.98    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0))),
% 3.61/0.98    inference(flattening,[],[f30])).
% 3.61/0.98  
% 3.61/0.98  fof(f38,plain,(
% 3.61/0.98    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) => (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,sK2),k3_xboole_0(X1,sK2)) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(X0))))) )),
% 3.61/0.98    introduced(choice_axiom,[])).
% 3.61/0.98  
% 3.61/0.98  fof(f37,plain,(
% 3.61/0.98    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) => (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),sK1,X2),k3_xboole_0(sK1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(X0))))) )),
% 3.61/0.98    introduced(choice_axiom,[])).
% 3.61/0.98  
% 3.61/0.98  fof(f36,plain,(
% 3.61/0.98    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) & v2_lattice3(k2_yellow_1(sK0)) & ~v1_xboole_0(sK0))),
% 3.61/0.98    introduced(choice_axiom,[])).
% 3.61/0.98  
% 3.61/0.98  fof(f39,plain,(
% 3.61/0.98    ((~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))) & v2_lattice3(k2_yellow_1(sK0)) & ~v1_xboole_0(sK0)),
% 3.61/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f38,f37,f36])).
% 3.61/0.98  
% 3.61/0.98  fof(f59,plain,(
% 3.61/0.98    ~v1_xboole_0(sK0)),
% 3.61/0.98    inference(cnf_transformation,[],[f39])).
% 3.61/0.98  
% 3.61/0.98  fof(f61,plain,(
% 3.61/0.98    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 3.61/0.98    inference(cnf_transformation,[],[f39])).
% 3.61/0.98  
% 3.61/0.98  fof(f11,axiom,(
% 3.61/0.98    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f55,plain,(
% 3.61/0.98    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 3.61/0.98    inference(cnf_transformation,[],[f11])).
% 3.61/0.98  
% 3.61/0.98  fof(f1,axiom,(
% 3.61/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f32,plain,(
% 3.61/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.61/0.98    inference(nnf_transformation,[],[f1])).
% 3.61/0.98  
% 3.61/0.98  fof(f33,plain,(
% 3.61/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.61/0.98    inference(flattening,[],[f32])).
% 3.61/0.98  
% 3.61/0.98  fof(f41,plain,(
% 3.61/0.98    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.61/0.98    inference(cnf_transformation,[],[f33])).
% 3.61/0.98  
% 3.61/0.98  fof(f66,plain,(
% 3.61/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.61/0.98    inference(equality_resolution,[],[f41])).
% 3.61/0.98  
% 3.61/0.98  fof(f58,plain,(
% 3.61/0.98    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f35])).
% 3.61/0.98  
% 3.61/0.98  fof(f8,axiom,(
% 3.61/0.98    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k12_lattice3(X0,X1,X2) = X1 <=> r3_orders_2(X0,X1,X2)))))),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f27,plain,(
% 3.61/0.98    ! [X0] : (! [X1] : (! [X2] : ((k12_lattice3(X0,X1,X2) = X1 <=> r3_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)))),
% 3.61/0.98    inference(ennf_transformation,[],[f8])).
% 3.61/0.98  
% 3.61/0.98  fof(f28,plain,(
% 3.61/0.98    ! [X0] : (! [X1] : (! [X2] : ((k12_lattice3(X0,X1,X2) = X1 <=> r3_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 3.61/0.98    inference(flattening,[],[f27])).
% 3.61/0.98  
% 3.61/0.98  fof(f34,plain,(
% 3.61/0.98    ! [X0] : (! [X1] : (! [X2] : (((k12_lattice3(X0,X1,X2) = X1 | ~r3_orders_2(X0,X1,X2)) & (r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) != X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 3.61/0.98    inference(nnf_transformation,[],[f28])).
% 3.61/0.98  
% 3.61/0.98  fof(f50,plain,(
% 3.61/0.98    ( ! [X2,X0,X1] : (k12_lattice3(X0,X1,X2) = X1 | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f34])).
% 3.61/0.98  
% 3.61/0.98  fof(f10,axiom,(
% 3.61/0.98    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f15,plain,(
% 3.61/0.98    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 3.61/0.98    inference(pure_predicate_removal,[],[f10])).
% 3.61/0.98  
% 3.61/0.98  fof(f52,plain,(
% 3.61/0.98    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 3.61/0.98    inference(cnf_transformation,[],[f15])).
% 3.61/0.98  
% 3.61/0.98  fof(f54,plain,(
% 3.61/0.98    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 3.61/0.98    inference(cnf_transformation,[],[f15])).
% 3.61/0.98  
% 3.61/0.98  fof(f9,axiom,(
% 3.61/0.98    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f16,plain,(
% 3.61/0.98    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 3.61/0.98    inference(pure_predicate_removal,[],[f9])).
% 3.61/0.98  
% 3.61/0.98  fof(f51,plain,(
% 3.61/0.98    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 3.61/0.98    inference(cnf_transformation,[],[f16])).
% 3.61/0.98  
% 3.61/0.98  fof(f60,plain,(
% 3.61/0.98    v2_lattice3(k2_yellow_1(sK0))),
% 3.61/0.98    inference(cnf_transformation,[],[f39])).
% 3.61/0.98  
% 3.61/0.98  fof(f5,axiom,(
% 3.61/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2))),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f21,plain,(
% 3.61/0.98    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 3.61/0.98    inference(ennf_transformation,[],[f5])).
% 3.61/0.98  
% 3.61/0.98  fof(f22,plain,(
% 3.61/0.98    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 3.61/0.98    inference(flattening,[],[f21])).
% 3.61/0.98  
% 3.61/0.98  fof(f46,plain,(
% 3.61/0.98    ( ! [X2,X0,X1] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f22])).
% 3.61/0.98  
% 3.61/0.98  fof(f62,plain,(
% 3.61/0.98    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 3.61/0.98    inference(cnf_transformation,[],[f39])).
% 3.61/0.98  
% 3.61/0.98  fof(f7,axiom,(
% 3.61/0.98    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (v4_orders_2(X0) => k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) = k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3))))))),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f25,plain,(
% 3.61/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) = k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) | ~v4_orders_2(X0)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 3.61/0.98    inference(ennf_transformation,[],[f7])).
% 3.61/0.98  
% 3.61/0.98  fof(f26,plain,(
% 3.61/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) = k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) | ~v4_orders_2(X0) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 3.61/0.98    inference(flattening,[],[f25])).
% 3.61/0.98  
% 3.61/0.98  fof(f48,plain,(
% 3.61/0.98    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) = k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) | ~v4_orders_2(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f26])).
% 3.61/0.98  
% 3.61/0.98  fof(f53,plain,(
% 3.61/0.98    ( ! [X0] : (v4_orders_2(k2_yellow_1(X0))) )),
% 3.61/0.98    inference(cnf_transformation,[],[f15])).
% 3.61/0.98  
% 3.61/0.98  fof(f49,plain,(
% 3.61/0.98    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) != X1 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f34])).
% 3.61/0.98  
% 3.61/0.98  fof(f6,axiom,(
% 3.61/0.98    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1))))),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f23,plain,(
% 3.61/0.98    ! [X0] : (! [X1] : (! [X2] : (k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 3.61/0.98    inference(ennf_transformation,[],[f6])).
% 3.61/0.98  
% 3.61/0.98  fof(f24,plain,(
% 3.61/0.98    ! [X0] : (! [X1] : (! [X2] : (k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 3.61/0.98    inference(flattening,[],[f23])).
% 3.61/0.98  
% 3.61/0.98  fof(f47,plain,(
% 3.61/0.98    ( ! [X2,X0,X1] : (k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f24])).
% 3.61/0.98  
% 3.61/0.98  fof(f4,axiom,(
% 3.61/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f19,plain,(
% 3.61/0.98    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 3.61/0.98    inference(ennf_transformation,[],[f4])).
% 3.61/0.98  
% 3.61/0.98  fof(f20,plain,(
% 3.61/0.98    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 3.61/0.98    inference(flattening,[],[f19])).
% 3.61/0.98  
% 3.61/0.98  fof(f45,plain,(
% 3.61/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f20])).
% 3.61/0.98  
% 3.61/0.98  fof(f2,axiom,(
% 3.61/0.98    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f17,plain,(
% 3.61/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 3.61/0.98    inference(ennf_transformation,[],[f2])).
% 3.61/0.98  
% 3.61/0.98  fof(f18,plain,(
% 3.61/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 3.61/0.98    inference(flattening,[],[f17])).
% 3.61/0.98  
% 3.61/0.98  fof(f43,plain,(
% 3.61/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f18])).
% 3.61/0.98  
% 3.61/0.98  fof(f3,axiom,(
% 3.61/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f44,plain,(
% 3.61/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.61/0.98    inference(cnf_transformation,[],[f3])).
% 3.61/0.98  
% 3.61/0.98  fof(f64,plain,(
% 3.61/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.61/0.98    inference(definition_unfolding,[],[f43,f44])).
% 3.61/0.98  
% 3.61/0.98  fof(f63,plain,(
% 3.61/0.98    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))),
% 3.61/0.98    inference(cnf_transformation,[],[f39])).
% 3.61/0.98  
% 3.61/0.98  fof(f65,plain,(
% 3.61/0.98    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k1_setfam_1(k2_tarski(sK1,sK2)))),
% 3.61/0.98    inference(definition_unfolding,[],[f63,f44])).
% 3.61/0.98  
% 3.61/0.98  cnf(c_16,plain,
% 3.61/0.98      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.61/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.61/0.98      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.61/0.98      | r1_tarski(X1,X2)
% 3.61/0.98      | v1_xboole_0(X0) ),
% 3.61/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_21,negated_conjecture,
% 3.61/0.98      ( ~ v1_xboole_0(sK0) ),
% 3.61/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_268,plain,
% 3.61/0.98      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.61/0.98      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.61/0.98      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.61/0.98      | r1_tarski(X1,X2)
% 3.61/0.98      | sK0 != X0 ),
% 3.61/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_269,plain,
% 3.61/0.98      ( ~ r3_orders_2(k2_yellow_1(sK0),X0,X1)
% 3.61/0.98      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
% 3.61/0.98      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
% 3.61/0.99      | r1_tarski(X0,X1) ),
% 3.61/0.99      inference(unflattening,[status(thm)],[c_268]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3735,plain,
% 3.61/0.99      ( ~ r3_orders_2(k2_yellow_1(sK0),X0,sK1)
% 3.61/0.99      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
% 3.61/0.99      | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
% 3.61/0.99      | r1_tarski(X0,sK1) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_269]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9051,plain,
% 3.61/0.99      ( ~ r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
% 3.61/0.99      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
% 3.61/0.99      | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
% 3.61/0.99      | r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_3735]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_19,negated_conjecture,
% 3.61/0.99      ( m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
% 3.61/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1226,plain,
% 3.61/0.99      ( m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_14,plain,
% 3.61/0.99      ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
% 3.61/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1238,plain,
% 3.61/0.99      ( m1_subset_1(sK1,sK0) = iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_1226,c_14]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1,plain,
% 3.61/0.99      ( r1_tarski(X0,X0) ),
% 3.61/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1230,plain,
% 3.61/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_15,plain,
% 3.61/0.99      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.61/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.61/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.61/0.99      | ~ r1_tarski(X1,X2)
% 3.61/0.99      | v1_xboole_0(X0) ),
% 3.61/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_284,plain,
% 3.61/0.99      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.61/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.61/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.61/0.99      | ~ r1_tarski(X1,X2)
% 3.61/0.99      | sK0 != X0 ),
% 3.61/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_21]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_285,plain,
% 3.61/0.99      ( r3_orders_2(k2_yellow_1(sK0),X0,X1)
% 3.61/0.99      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
% 3.61/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
% 3.61/0.99      | ~ r1_tarski(X0,X1) ),
% 3.61/0.99      inference(unflattening,[status(thm)],[c_284]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1222,plain,
% 3.61/0.99      ( r3_orders_2(k2_yellow_1(sK0),X0,X1) = iProver_top
% 3.61/0.99      | m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) != iProver_top
% 3.61/0.99      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) != iProver_top
% 3.61/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_285]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1265,plain,
% 3.61/0.99      ( r3_orders_2(k2_yellow_1(sK0),X0,X1) = iProver_top
% 3.61/0.99      | m1_subset_1(X0,sK0) != iProver_top
% 3.61/0.99      | m1_subset_1(X1,sK0) != iProver_top
% 3.61/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_1222,c_14]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_8,plain,
% 3.61/0.99      ( ~ r3_orders_2(X0,X1,X2)
% 3.61/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.61/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.61/0.99      | ~ v3_orders_2(X0)
% 3.61/0.99      | ~ v5_orders_2(X0)
% 3.61/0.99      | ~ v2_lattice3(X0)
% 3.61/0.99      | ~ l1_orders_2(X0)
% 3.61/0.99      | k12_lattice3(X0,X1,X2) = X1 ),
% 3.61/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_13,plain,
% 3.61/0.99      ( v3_orders_2(k2_yellow_1(X0)) ),
% 3.61/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_339,plain,
% 3.61/0.99      ( ~ r3_orders_2(X0,X1,X2)
% 3.61/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.61/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.61/0.99      | ~ v5_orders_2(X0)
% 3.61/0.99      | ~ v2_lattice3(X0)
% 3.61/0.99      | ~ l1_orders_2(X0)
% 3.61/0.99      | k12_lattice3(X0,X1,X2) = X1
% 3.61/0.99      | k2_yellow_1(X3) != X0 ),
% 3.61/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_13]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_340,plain,
% 3.61/0.99      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.61/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.61/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.61/0.99      | ~ v5_orders_2(k2_yellow_1(X0))
% 3.61/0.99      | ~ v2_lattice3(k2_yellow_1(X0))
% 3.61/0.99      | ~ l1_orders_2(k2_yellow_1(X0))
% 3.61/0.99      | k12_lattice3(k2_yellow_1(X0),X1,X2) = X1 ),
% 3.61/0.99      inference(unflattening,[status(thm)],[c_339]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_11,plain,
% 3.61/0.99      ( v5_orders_2(k2_yellow_1(X0)) ),
% 3.61/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_10,plain,
% 3.61/0.99      ( l1_orders_2(k2_yellow_1(X0)) ),
% 3.61/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_344,plain,
% 3.61/0.99      ( ~ v2_lattice3(k2_yellow_1(X0))
% 3.61/0.99      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.61/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.61/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.61/0.99      | k12_lattice3(k2_yellow_1(X0),X1,X2) = X1 ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_340,c_11,c_10]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_345,plain,
% 3.61/0.99      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.61/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.61/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.61/0.99      | ~ v2_lattice3(k2_yellow_1(X0))
% 3.61/0.99      | k12_lattice3(k2_yellow_1(X0),X1,X2) = X1 ),
% 3.61/0.99      inference(renaming,[status(thm)],[c_344]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1220,plain,
% 3.61/0.99      ( k12_lattice3(k2_yellow_1(X0),X1,X2) = X1
% 3.61/0.99      | r3_orders_2(k2_yellow_1(X0),X1,X2) != iProver_top
% 3.61/0.99      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.61/0.99      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.61/0.99      | v2_lattice3(k2_yellow_1(X0)) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_345]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1301,plain,
% 3.61/0.99      ( k12_lattice3(k2_yellow_1(X0),X1,X2) = X1
% 3.61/0.99      | r3_orders_2(k2_yellow_1(X0),X1,X2) != iProver_top
% 3.61/0.99      | m1_subset_1(X1,X0) != iProver_top
% 3.61/0.99      | m1_subset_1(X2,X0) != iProver_top
% 3.61/0.99      | v2_lattice3(k2_yellow_1(X0)) != iProver_top ),
% 3.61/0.99      inference(light_normalisation,[status(thm)],[c_1220,c_14]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3210,plain,
% 3.61/0.99      ( k12_lattice3(k2_yellow_1(sK0),X0,X1) = X0
% 3.61/0.99      | m1_subset_1(X0,sK0) != iProver_top
% 3.61/0.99      | m1_subset_1(X1,sK0) != iProver_top
% 3.61/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.61/0.99      | v2_lattice3(k2_yellow_1(sK0)) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1265,c_1301]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_20,negated_conjecture,
% 3.61/0.99      ( v2_lattice3(k2_yellow_1(sK0)) ),
% 3.61/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_23,plain,
% 3.61/0.99      ( v2_lattice3(k2_yellow_1(sK0)) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_7361,plain,
% 3.61/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.61/0.99      | m1_subset_1(X1,sK0) != iProver_top
% 3.61/0.99      | m1_subset_1(X0,sK0) != iProver_top
% 3.61/0.99      | k12_lattice3(k2_yellow_1(sK0),X0,X1) = X0 ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_3210,c_23]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_7362,plain,
% 3.61/0.99      ( k12_lattice3(k2_yellow_1(sK0),X0,X1) = X0
% 3.61/0.99      | m1_subset_1(X0,sK0) != iProver_top
% 3.61/0.99      | m1_subset_1(X1,sK0) != iProver_top
% 3.61/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.61/0.99      inference(renaming,[status(thm)],[c_7361]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_7371,plain,
% 3.61/0.99      ( k12_lattice3(k2_yellow_1(sK0),X0,X0) = X0
% 3.61/0.99      | m1_subset_1(X0,sK0) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1230,c_7362]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_7396,plain,
% 3.61/0.99      ( k12_lattice3(k2_yellow_1(sK0),sK1,sK1) = sK1 ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1238,c_7371]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_5,plain,
% 3.61/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.61/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.61/0.99      | ~ v5_orders_2(X1)
% 3.61/0.99      | ~ v2_lattice3(X1)
% 3.61/0.99      | ~ l1_orders_2(X1)
% 3.61/0.99      | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0) ),
% 3.61/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_401,plain,
% 3.61/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.61/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.61/0.99      | ~ v2_lattice3(X1)
% 3.61/0.99      | ~ l1_orders_2(X1)
% 3.61/0.99      | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0)
% 3.61/0.99      | k2_yellow_1(X3) != X1 ),
% 3.61/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_11]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_402,plain,
% 3.61/0.99      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
% 3.61/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
% 3.61/0.99      | ~ v2_lattice3(k2_yellow_1(X1))
% 3.61/0.99      | ~ l1_orders_2(k2_yellow_1(X1))
% 3.61/0.99      | k12_lattice3(k2_yellow_1(X1),X0,X2) = k11_lattice3(k2_yellow_1(X1),X0,X2) ),
% 3.61/0.99      inference(unflattening,[status(thm)],[c_401]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_416,plain,
% 3.61/0.99      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
% 3.61/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
% 3.61/0.99      | ~ v2_lattice3(k2_yellow_1(X1))
% 3.61/0.99      | k12_lattice3(k2_yellow_1(X1),X0,X2) = k11_lattice3(k2_yellow_1(X1),X0,X2) ),
% 3.61/0.99      inference(forward_subsumption_resolution,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_402,c_10]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1218,plain,
% 3.61/0.99      ( k12_lattice3(k2_yellow_1(X0),X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2)
% 3.61/0.99      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.61/0.99      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.61/0.99      | v2_lattice3(k2_yellow_1(X0)) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_416]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1283,plain,
% 3.61/0.99      ( k12_lattice3(k2_yellow_1(X0),X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2)
% 3.61/0.99      | m1_subset_1(X1,X0) != iProver_top
% 3.61/0.99      | m1_subset_1(X2,X0) != iProver_top
% 3.61/0.99      | v2_lattice3(k2_yellow_1(X0)) != iProver_top ),
% 3.61/0.99      inference(light_normalisation,[status(thm)],[c_1218,c_14]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2030,plain,
% 3.61/0.99      ( k12_lattice3(k2_yellow_1(sK0),sK1,X0) = k11_lattice3(k2_yellow_1(sK0),sK1,X0)
% 3.61/0.99      | m1_subset_1(X0,sK0) != iProver_top
% 3.61/0.99      | v2_lattice3(k2_yellow_1(sK0)) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1238,c_1283]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2566,plain,
% 3.61/0.99      ( m1_subset_1(X0,sK0) != iProver_top
% 3.61/0.99      | k12_lattice3(k2_yellow_1(sK0),sK1,X0) = k11_lattice3(k2_yellow_1(sK0),sK1,X0) ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_2030,c_23]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2567,plain,
% 3.61/0.99      ( k12_lattice3(k2_yellow_1(sK0),sK1,X0) = k11_lattice3(k2_yellow_1(sK0),sK1,X0)
% 3.61/0.99      | m1_subset_1(X0,sK0) != iProver_top ),
% 3.61/0.99      inference(renaming,[status(thm)],[c_2566]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2574,plain,
% 3.61/0.99      ( k12_lattice3(k2_yellow_1(sK0),sK1,sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,sK1) ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1238,c_2567]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_7523,plain,
% 3.61/0.99      ( k11_lattice3(k2_yellow_1(sK0),sK1,sK1) = sK1 ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_7396,c_2574]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_18,negated_conjecture,
% 3.61/0.99      ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
% 3.61/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1227,plain,
% 3.61/0.99      ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1241,plain,
% 3.61/0.99      ( m1_subset_1(sK2,sK0) = iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_1227,c_14]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_7,plain,
% 3.61/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.61/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.61/0.99      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 3.61/0.99      | ~ v4_orders_2(X1)
% 3.61/0.99      | ~ v5_orders_2(X1)
% 3.61/0.99      | ~ v2_lattice3(X1)
% 3.61/0.99      | ~ l1_orders_2(X1)
% 3.61/0.99      | k11_lattice3(X1,k11_lattice3(X1,X2,X0),X3) = k11_lattice3(X1,X2,k11_lattice3(X1,X0,X3)) ),
% 3.61/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_12,plain,
% 3.61/0.99      ( v4_orders_2(k2_yellow_1(X0)) ),
% 3.61/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_234,plain,
% 3.61/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.61/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.61/0.99      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 3.61/0.99      | ~ v5_orders_2(X1)
% 3.61/0.99      | ~ v2_lattice3(X1)
% 3.61/0.99      | ~ l1_orders_2(X1)
% 3.61/0.99      | k11_lattice3(X1,X2,k11_lattice3(X1,X0,X3)) = k11_lattice3(X1,k11_lattice3(X1,X2,X0),X3)
% 3.61/0.99      | k2_yellow_1(X4) != X1 ),
% 3.61/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_12]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_235,plain,
% 3.61/0.99      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
% 3.61/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
% 3.61/0.99      | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
% 3.61/0.99      | ~ v5_orders_2(k2_yellow_1(X1))
% 3.61/0.99      | ~ v2_lattice3(k2_yellow_1(X1))
% 3.61/0.99      | ~ l1_orders_2(k2_yellow_1(X1))
% 3.61/0.99      | k11_lattice3(k2_yellow_1(X1),X2,k11_lattice3(k2_yellow_1(X1),X3,X0)) = k11_lattice3(k2_yellow_1(X1),k11_lattice3(k2_yellow_1(X1),X2,X3),X0) ),
% 3.61/0.99      inference(unflattening,[status(thm)],[c_234]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_253,plain,
% 3.61/0.99      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
% 3.61/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
% 3.61/0.99      | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
% 3.61/0.99      | ~ v2_lattice3(k2_yellow_1(X1))
% 3.61/0.99      | k11_lattice3(k2_yellow_1(X1),X2,k11_lattice3(k2_yellow_1(X1),X3,X0)) = k11_lattice3(k2_yellow_1(X1),k11_lattice3(k2_yellow_1(X1),X2,X3),X0) ),
% 3.61/0.99      inference(forward_subsumption_resolution,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_235,c_10,c_11]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1224,plain,
% 3.61/0.99      ( k11_lattice3(k2_yellow_1(X0),X1,k11_lattice3(k2_yellow_1(X0),X2,X3)) = k11_lattice3(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X3)
% 3.61/0.99      | m1_subset_1(X3,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.61/0.99      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.61/0.99      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.61/0.99      | v2_lattice3(k2_yellow_1(X0)) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_253]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1323,plain,
% 3.61/0.99      ( k11_lattice3(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X3) = k11_lattice3(k2_yellow_1(X0),X1,k11_lattice3(k2_yellow_1(X0),X2,X3))
% 3.61/0.99      | m1_subset_1(X1,X0) != iProver_top
% 3.61/0.99      | m1_subset_1(X2,X0) != iProver_top
% 3.61/0.99      | m1_subset_1(X3,X0) != iProver_top
% 3.61/0.99      | v2_lattice3(k2_yellow_1(X0)) != iProver_top ),
% 3.61/0.99      inference(light_normalisation,[status(thm)],[c_1224,c_14]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3305,plain,
% 3.61/0.99      ( k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,X0),X1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),X0,X1))
% 3.61/0.99      | m1_subset_1(X0,sK0) != iProver_top
% 3.61/0.99      | m1_subset_1(X1,sK0) != iProver_top
% 3.61/0.99      | v2_lattice3(k2_yellow_1(sK0)) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1238,c_1323]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4438,plain,
% 3.61/0.99      ( m1_subset_1(X1,sK0) != iProver_top
% 3.61/0.99      | m1_subset_1(X0,sK0) != iProver_top
% 3.61/0.99      | k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,X0),X1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),X0,X1)) ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_3305,c_23]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4439,plain,
% 3.61/0.99      ( k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,X0),X1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),X0,X1))
% 3.61/0.99      | m1_subset_1(X0,sK0) != iProver_top
% 3.61/0.99      | m1_subset_1(X1,sK0) != iProver_top ),
% 3.61/0.99      inference(renaming,[status(thm)],[c_4438]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4447,plain,
% 3.61/0.99      ( k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,X0)) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK1),X0)
% 3.61/0.99      | m1_subset_1(X0,sK0) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1238,c_4439]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4499,plain,
% 3.61/0.99      ( k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK1),sK2) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1241,c_4447]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_7689,plain,
% 3.61/0.99      ( k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) = k11_lattice3(k2_yellow_1(sK0),sK1,sK2) ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_7523,c_4499]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2031,plain,
% 3.61/0.99      ( k12_lattice3(k2_yellow_1(sK0),sK2,X0) = k11_lattice3(k2_yellow_1(sK0),sK2,X0)
% 3.61/0.99      | m1_subset_1(X0,sK0) != iProver_top
% 3.61/0.99      | v2_lattice3(k2_yellow_1(sK0)) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1241,c_1283]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2733,plain,
% 3.61/0.99      ( m1_subset_1(X0,sK0) != iProver_top
% 3.61/0.99      | k12_lattice3(k2_yellow_1(sK0),sK2,X0) = k11_lattice3(k2_yellow_1(sK0),sK2,X0) ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_2031,c_23]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2734,plain,
% 3.61/0.99      ( k12_lattice3(k2_yellow_1(sK0),sK2,X0) = k11_lattice3(k2_yellow_1(sK0),sK2,X0)
% 3.61/0.99      | m1_subset_1(X0,sK0) != iProver_top ),
% 3.61/0.99      inference(renaming,[status(thm)],[c_2733]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2742,plain,
% 3.61/0.99      ( k12_lattice3(k2_yellow_1(sK0),sK2,sK2) = k11_lattice3(k2_yellow_1(sK0),sK2,sK2) ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1241,c_2734]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9,plain,
% 3.61/0.99      ( r3_orders_2(X0,X1,X2)
% 3.61/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.61/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.61/0.99      | ~ v3_orders_2(X0)
% 3.61/0.99      | ~ v5_orders_2(X0)
% 3.61/0.99      | ~ v2_lattice3(X0)
% 3.61/0.99      | ~ l1_orders_2(X0)
% 3.61/0.99      | k12_lattice3(X0,X1,X2) != X1 ),
% 3.61/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_312,plain,
% 3.61/0.99      ( r3_orders_2(X0,X1,X2)
% 3.61/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.61/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.61/0.99      | ~ v5_orders_2(X0)
% 3.61/0.99      | ~ v2_lattice3(X0)
% 3.61/0.99      | ~ l1_orders_2(X0)
% 3.61/0.99      | k12_lattice3(X0,X1,X2) != X1
% 3.61/0.99      | k2_yellow_1(X3) != X0 ),
% 3.61/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_13]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_313,plain,
% 3.61/0.99      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.61/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.61/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.61/0.99      | ~ v5_orders_2(k2_yellow_1(X0))
% 3.61/0.99      | ~ v2_lattice3(k2_yellow_1(X0))
% 3.61/0.99      | ~ l1_orders_2(k2_yellow_1(X0))
% 3.61/0.99      | k12_lattice3(k2_yellow_1(X0),X1,X2) != X1 ),
% 3.61/0.99      inference(unflattening,[status(thm)],[c_312]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_317,plain,
% 3.61/0.99      ( ~ v2_lattice3(k2_yellow_1(X0))
% 3.61/0.99      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.61/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.61/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.61/0.99      | k12_lattice3(k2_yellow_1(X0),X1,X2) != X1 ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_313,c_11,c_10]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_318,plain,
% 3.61/0.99      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.61/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.61/0.99      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.61/0.99      | ~ v2_lattice3(k2_yellow_1(X0))
% 3.61/0.99      | k12_lattice3(k2_yellow_1(X0),X1,X2) != X1 ),
% 3.61/0.99      inference(renaming,[status(thm)],[c_317]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1221,plain,
% 3.61/0.99      ( k12_lattice3(k2_yellow_1(X0),X1,X2) != X1
% 3.61/0.99      | r3_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
% 3.61/0.99      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.61/0.99      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.61/0.99      | v2_lattice3(k2_yellow_1(X0)) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_318]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1312,plain,
% 3.61/0.99      ( k12_lattice3(k2_yellow_1(X0),X1,X2) != X1
% 3.61/0.99      | r3_orders_2(k2_yellow_1(X0),X1,X2) = iProver_top
% 3.61/0.99      | m1_subset_1(X1,X0) != iProver_top
% 3.61/0.99      | m1_subset_1(X2,X0) != iProver_top
% 3.61/0.99      | v2_lattice3(k2_yellow_1(X0)) != iProver_top ),
% 3.61/0.99      inference(light_normalisation,[status(thm)],[c_1221,c_14]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3255,plain,
% 3.61/0.99      ( k11_lattice3(k2_yellow_1(sK0),sK2,sK2) != sK2
% 3.61/0.99      | r3_orders_2(k2_yellow_1(sK0),sK2,sK2) = iProver_top
% 3.61/0.99      | m1_subset_1(sK2,sK0) != iProver_top
% 3.61/0.99      | v2_lattice3(k2_yellow_1(sK0)) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_2742,c_1312]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_25,plain,
% 3.61/0.99      ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1385,plain,
% 3.61/0.99      ( r3_orders_2(k2_yellow_1(sK0),sK2,X0)
% 3.61/0.99      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
% 3.61/0.99      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
% 3.61/0.99      | ~ r1_tarski(sK2,X0) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_285]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1638,plain,
% 3.61/0.99      ( r3_orders_2(k2_yellow_1(sK0),sK2,sK2)
% 3.61/0.99      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
% 3.61/0.99      | ~ r1_tarski(sK2,sK2) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_1385]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1640,plain,
% 3.61/0.99      ( r3_orders_2(k2_yellow_1(sK0),sK2,sK2) = iProver_top
% 3.61/0.99      | m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) != iProver_top
% 3.61/0.99      | r1_tarski(sK2,sK2) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_1638]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1639,plain,
% 3.61/0.99      ( r1_tarski(sK2,sK2) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1642,plain,
% 3.61/0.99      ( r1_tarski(sK2,sK2) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_1639]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4962,plain,
% 3.61/0.99      ( r3_orders_2(k2_yellow_1(sK0),sK2,sK2) = iProver_top ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_3255,c_25,c_1640,c_1642]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4967,plain,
% 3.61/0.99      ( k12_lattice3(k2_yellow_1(sK0),sK2,sK2) = sK2
% 3.61/0.99      | m1_subset_1(sK2,sK0) != iProver_top
% 3.61/0.99      | v2_lattice3(k2_yellow_1(sK0)) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_4962,c_1301]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4974,plain,
% 3.61/0.99      ( k11_lattice3(k2_yellow_1(sK0),sK2,sK2) = sK2
% 3.61/0.99      | m1_subset_1(sK2,sK0) != iProver_top
% 3.61/0.99      | v2_lattice3(k2_yellow_1(sK0)) != iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_4967,c_2742]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6240,plain,
% 3.61/0.99      ( k11_lattice3(k2_yellow_1(sK0),sK2,sK2) = sK2 ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_4974,c_23,c_1241]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3306,plain,
% 3.61/0.99      ( k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK2,X0),X1) = k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),X0,X1))
% 3.61/0.99      | m1_subset_1(X0,sK0) != iProver_top
% 3.61/0.99      | m1_subset_1(X1,sK0) != iProver_top
% 3.61/0.99      | v2_lattice3(k2_yellow_1(sK0)) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1241,c_1323]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4575,plain,
% 3.61/0.99      ( m1_subset_1(X1,sK0) != iProver_top
% 3.61/0.99      | m1_subset_1(X0,sK0) != iProver_top
% 3.61/0.99      | k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK2,X0),X1) = k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),X0,X1)) ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_3306,c_23]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4576,plain,
% 3.61/0.99      ( k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK2,X0),X1) = k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),X0,X1))
% 3.61/0.99      | m1_subset_1(X0,sK0) != iProver_top
% 3.61/0.99      | m1_subset_1(X1,sK0) != iProver_top ),
% 3.61/0.99      inference(renaming,[status(thm)],[c_4575]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4585,plain,
% 3.61/0.99      ( k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK2,X0)) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK2,sK2),X0)
% 3.61/0.99      | m1_subset_1(X0,sK0) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1241,c_4576]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4793,plain,
% 3.61/0.99      ( k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK2,sK2),sK1) = k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK2,sK1)) ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1238,c_4585]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6,plain,
% 3.61/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.61/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.61/0.99      | ~ v5_orders_2(X1)
% 3.61/0.99      | ~ v2_lattice3(X1)
% 3.61/0.99      | ~ l1_orders_2(X1)
% 3.61/0.99      | k11_lattice3(X1,X0,X2) = k11_lattice3(X1,X2,X0) ),
% 3.61/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_378,plain,
% 3.61/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.61/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.61/0.99      | ~ v2_lattice3(X1)
% 3.61/0.99      | ~ l1_orders_2(X1)
% 3.61/0.99      | k11_lattice3(X1,X0,X2) = k11_lattice3(X1,X2,X0)
% 3.61/0.99      | k2_yellow_1(X3) != X1 ),
% 3.61/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_11]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_379,plain,
% 3.61/0.99      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
% 3.61/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
% 3.61/0.99      | ~ v2_lattice3(k2_yellow_1(X1))
% 3.61/0.99      | ~ l1_orders_2(k2_yellow_1(X1))
% 3.61/0.99      | k11_lattice3(k2_yellow_1(X1),X2,X0) = k11_lattice3(k2_yellow_1(X1),X0,X2) ),
% 3.61/0.99      inference(unflattening,[status(thm)],[c_378]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_393,plain,
% 3.61/0.99      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
% 3.61/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
% 3.61/0.99      | ~ v2_lattice3(k2_yellow_1(X1))
% 3.61/0.99      | k11_lattice3(k2_yellow_1(X1),X2,X0) = k11_lattice3(k2_yellow_1(X1),X0,X2) ),
% 3.61/0.99      inference(forward_subsumption_resolution,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_379,c_10]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1219,plain,
% 3.61/0.99      ( k11_lattice3(k2_yellow_1(X0),X1,X2) = k11_lattice3(k2_yellow_1(X0),X2,X1)
% 3.61/0.99      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.61/0.99      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.61/0.99      | v2_lattice3(k2_yellow_1(X0)) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_393]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1292,plain,
% 3.61/0.99      ( k11_lattice3(k2_yellow_1(X0),X1,X2) = k11_lattice3(k2_yellow_1(X0),X2,X1)
% 3.61/0.99      | m1_subset_1(X2,X0) != iProver_top
% 3.61/0.99      | m1_subset_1(X1,X0) != iProver_top
% 3.61/0.99      | v2_lattice3(k2_yellow_1(X0)) != iProver_top ),
% 3.61/0.99      inference(light_normalisation,[status(thm)],[c_1219,c_14]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3170,plain,
% 3.61/0.99      ( k11_lattice3(k2_yellow_1(sK0),X0,sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,X0)
% 3.61/0.99      | m1_subset_1(X0,sK0) != iProver_top
% 3.61/0.99      | v2_lattice3(k2_yellow_1(sK0)) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1238,c_1292]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3614,plain,
% 3.61/0.99      ( m1_subset_1(X0,sK0) != iProver_top
% 3.61/0.99      | k11_lattice3(k2_yellow_1(sK0),X0,sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,X0) ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_3170,c_23]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3615,plain,
% 3.61/0.99      ( k11_lattice3(k2_yellow_1(sK0),X0,sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,X0)
% 3.61/0.99      | m1_subset_1(X0,sK0) != iProver_top ),
% 3.61/0.99      inference(renaming,[status(thm)],[c_3614]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3623,plain,
% 3.61/0.99      ( k11_lattice3(k2_yellow_1(sK0),sK2,sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,sK2) ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1241,c_3615]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4805,plain,
% 3.61/0.99      ( k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK2,sK2),sK1) ),
% 3.61/0.99      inference(light_normalisation,[status(thm)],[c_4793,c_3623]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4,plain,
% 3.61/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.61/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.61/0.99      | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
% 3.61/0.99      | ~ l1_orders_2(X1) ),
% 3.61/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_434,plain,
% 3.61/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.61/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.61/0.99      | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
% 3.61/0.99      | k2_yellow_1(X3) != X1 ),
% 3.61/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_10]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_435,plain,
% 3.61/0.99      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
% 3.61/0.99      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
% 3.61/0.99      | m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),u1_struct_0(k2_yellow_1(X1))) ),
% 3.61/0.99      inference(unflattening,[status(thm)],[c_434]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1217,plain,
% 3.61/0.99      ( m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) != iProver_top
% 3.61/0.99      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) != iProver_top
% 3.61/0.99      | m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),u1_struct_0(k2_yellow_1(X1))) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_435]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1258,plain,
% 3.61/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 3.61/0.99      | m1_subset_1(X2,X1) != iProver_top
% 3.61/0.99      | m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),X1) = iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_1217,c_14]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4861,plain,
% 3.61/0.99      ( m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)),sK0) = iProver_top
% 3.61/0.99      | m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK2,sK2),sK0) != iProver_top
% 3.61/0.99      | m1_subset_1(sK1,sK0) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_4805,c_1258]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_5731,plain,
% 3.61/0.99      ( m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK2,sK2),sK0) != iProver_top
% 3.61/0.99      | m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)),sK0) = iProver_top ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_4861,c_1238]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_5732,plain,
% 3.61/0.99      ( m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)),sK0) = iProver_top
% 3.61/0.99      | m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK2,sK2),sK0) != iProver_top ),
% 3.61/0.99      inference(renaming,[status(thm)],[c_5731]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4584,plain,
% 3.61/0.99      ( k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,X0)) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK2,sK1),X0)
% 3.61/0.99      | m1_subset_1(X0,sK0) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1238,c_4576]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4601,plain,
% 3.61/0.99      ( k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,X0)) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),X0)
% 3.61/0.99      | m1_subset_1(X0,sK0) != iProver_top ),
% 3.61/0.99      inference(light_normalisation,[status(thm)],[c_4584,c_3623]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4867,plain,
% 3.61/0.99      ( k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) = k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1241,c_4601]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4448,plain,
% 3.61/0.99      ( k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK2,X0)) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),X0)
% 3.61/0.99      | m1_subset_1(X0,sK0) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1241,c_4439]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4550,plain,
% 3.61/0.99      ( k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK2,sK2)) ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1241,c_4448]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4876,plain,
% 3.61/0.99      ( k11_lattice3(k2_yellow_1(sK0),sK2,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK2,sK2)) ),
% 3.61/0.99      inference(light_normalisation,[status(thm)],[c_4867,c_4550]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_5735,plain,
% 3.61/0.99      ( m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK2,sK2),sK0) != iProver_top
% 3.61/0.99      | m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK2,sK2)),sK0) = iProver_top ),
% 3.61/0.99      inference(light_normalisation,[status(thm)],[c_5732,c_4876]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6247,plain,
% 3.61/0.99      ( m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) = iProver_top
% 3.61/0.99      | m1_subset_1(sK2,sK0) != iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_6240,c_5735]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6275,plain,
% 3.61/0.99      ( m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
% 3.61/0.99      | ~ m1_subset_1(sK2,sK0) ),
% 3.61/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_6247]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2032,plain,
% 3.61/0.99      ( k12_lattice3(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X3) = k11_lattice3(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X3)
% 3.61/0.99      | m1_subset_1(X1,X0) != iProver_top
% 3.61/0.99      | m1_subset_1(X2,X0) != iProver_top
% 3.61/0.99      | m1_subset_1(X3,X0) != iProver_top
% 3.61/0.99      | v2_lattice3(k2_yellow_1(X0)) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1258,c_1283]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4921,plain,
% 3.61/0.99      ( k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,X0),X1) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,X0),X1)
% 3.61/0.99      | m1_subset_1(X0,sK0) != iProver_top
% 3.61/0.99      | m1_subset_1(X1,sK0) != iProver_top
% 3.61/0.99      | v2_lattice3(k2_yellow_1(sK0)) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1238,c_2032]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_5306,plain,
% 3.61/0.99      ( m1_subset_1(X1,sK0) != iProver_top
% 3.61/0.99      | m1_subset_1(X0,sK0) != iProver_top
% 3.61/0.99      | k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,X0),X1) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,X0),X1) ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_4921,c_23]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_5307,plain,
% 3.61/0.99      ( k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,X0),X1) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,X0),X1)
% 3.61/0.99      | m1_subset_1(X0,sK0) != iProver_top
% 3.61/0.99      | m1_subset_1(X1,sK0) != iProver_top ),
% 3.61/0.99      inference(renaming,[status(thm)],[c_5306]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_5316,plain,
% 3.61/0.99      ( k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),X0) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),X0)
% 3.61/0.99      | m1_subset_1(X0,sK0) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1241,c_5307]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_5406,plain,
% 3.61/0.99      ( k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1241,c_5316]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_5425,plain,
% 3.61/0.99      ( k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK2,sK2)) ),
% 3.61/0.99      inference(light_normalisation,[status(thm)],[c_5406,c_4550]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6246,plain,
% 3.61/0.99      ( k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) = k11_lattice3(k2_yellow_1(sK0),sK1,sK2) ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_6240,c_5425]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_5405,plain,
% 3.61/0.99      ( k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) = k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1238,c_5316]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4549,plain,
% 3.61/0.99      ( k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK2,sK1)) ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1238,c_4448]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4561,plain,
% 3.61/0.99      ( k11_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
% 3.61/0.99      inference(light_normalisation,[status(thm)],[c_4549,c_3623]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_5428,plain,
% 3.61/0.99      ( k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) = k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
% 3.61/0.99      inference(light_normalisation,[status(thm)],[c_5405,c_4561]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6113,plain,
% 3.61/0.99      ( k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) != k11_lattice3(k2_yellow_1(sK0),sK1,sK2)
% 3.61/0.99      | r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) = iProver_top
% 3.61/0.99      | m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) != iProver_top
% 3.61/0.99      | m1_subset_1(sK1,sK0) != iProver_top
% 3.61/0.99      | v2_lattice3(k2_yellow_1(sK0)) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_5428,c_1312]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6114,plain,
% 3.61/0.99      ( r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
% 3.61/0.99      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
% 3.61/0.99      | ~ m1_subset_1(sK1,sK0)
% 3.61/0.99      | ~ v2_lattice3(k2_yellow_1(sK0))
% 3.61/0.99      | k11_lattice3(k2_yellow_1(sK0),sK1,k11_lattice3(k2_yellow_1(sK0),sK1,sK2)) != k11_lattice3(k2_yellow_1(sK0),sK1,sK2) ),
% 3.61/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_6113]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1456,plain,
% 3.61/0.99      ( r3_orders_2(k2_yellow_1(sK0),X0,sK2)
% 3.61/0.99      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
% 3.61/0.99      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
% 3.61/0.99      | ~ v2_lattice3(k2_yellow_1(sK0))
% 3.61/0.99      | k12_lattice3(k2_yellow_1(sK0),X0,sK2) != X0 ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_318]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1991,plain,
% 3.61/0.99      ( r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
% 3.61/0.99      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
% 3.61/0.99      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
% 3.61/0.99      | ~ v2_lattice3(k2_yellow_1(sK0))
% 3.61/0.99      | k12_lattice3(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) != k11_lattice3(k2_yellow_1(sK0),sK1,sK2) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_1456]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1412,plain,
% 3.61/0.99      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
% 3.61/0.99      | m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,X0),u1_struct_0(k2_yellow_1(sK0)))
% 3.61/0.99      | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_435]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1621,plain,
% 3.61/0.99      ( m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
% 3.61/0.99      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
% 3.61/0.99      | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_1412]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1498,plain,
% 3.61/0.99      ( ~ r3_orders_2(k2_yellow_1(sK0),k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
% 3.61/0.99      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
% 3.61/0.99      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
% 3.61/0.99      | r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_269]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3,plain,
% 3.61/0.99      ( ~ r1_tarski(X0,X1)
% 3.61/0.99      | ~ r1_tarski(X0,X2)
% 3.61/0.99      | r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) ),
% 3.61/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1404,plain,
% 3.61/0.99      ( r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k1_setfam_1(k2_tarski(sK1,sK2)))
% 3.61/0.99      | ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK2)
% 3.61/0.99      | ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1354,plain,
% 3.61/0.99      ( m1_subset_1(sK2,sK0) ),
% 3.61/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1241]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1353,plain,
% 3.61/0.99      ( m1_subset_1(sK1,sK0) ),
% 3.61/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1238]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_17,negated_conjecture,
% 3.61/0.99      ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k1_setfam_1(k2_tarski(sK1,sK2))) ),
% 3.61/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(contradiction,plain,
% 3.61/0.99      ( $false ),
% 3.61/0.99      inference(minisat,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_9051,c_7689,c_6275,c_6246,c_6114,c_1991,c_1621,c_1498,
% 3.61/0.99                 c_1404,c_1354,c_1353,c_17,c_18,c_19,c_20]) ).
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.61/0.99  
% 3.61/0.99  ------                               Statistics
% 3.61/0.99  
% 3.61/0.99  ------ General
% 3.61/0.99  
% 3.61/0.99  abstr_ref_over_cycles:                  0
% 3.61/0.99  abstr_ref_under_cycles:                 0
% 3.61/0.99  gc_basic_clause_elim:                   0
% 3.61/0.99  forced_gc_time:                         0
% 3.61/0.99  parsing_time:                           0.011
% 3.61/0.99  unif_index_cands_time:                  0.
% 3.61/0.99  unif_index_add_time:                    0.
% 3.61/0.99  orderings_time:                         0.
% 3.61/0.99  out_proof_time:                         0.015
% 3.61/0.99  total_time:                             0.27
% 3.61/0.99  num_of_symbols:                         49
% 3.61/0.99  num_of_terms:                           8113
% 3.61/0.99  
% 3.61/0.99  ------ Preprocessing
% 3.61/0.99  
% 3.61/0.99  num_of_splits:                          0
% 3.61/0.99  num_of_split_atoms:                     0
% 3.61/0.99  num_of_reused_defs:                     0
% 3.61/0.99  num_eq_ax_congr_red:                    13
% 3.61/0.99  num_of_sem_filtered_clauses:            1
% 3.61/0.99  num_of_subtypes:                        0
% 3.61/0.99  monotx_restored_types:                  0
% 3.61/0.99  sat_num_of_epr_types:                   0
% 3.61/0.99  sat_num_of_non_cyclic_types:            0
% 3.61/0.99  sat_guarded_non_collapsed_types:        0
% 3.61/0.99  num_pure_diseq_elim:                    0
% 3.61/0.99  simp_replaced_by:                       0
% 3.61/0.99  res_preprocessed:                       94
% 3.61/0.99  prep_upred:                             0
% 3.61/0.99  prep_unflattend:                        16
% 3.61/0.99  smt_new_axioms:                         0
% 3.61/0.99  pred_elim_cands:                        4
% 3.61/0.99  pred_elim:                              5
% 3.61/0.99  pred_elim_cl:                           5
% 3.61/0.99  pred_elim_cycles:                       9
% 3.61/0.99  merged_defs:                            0
% 3.61/0.99  merged_defs_ncl:                        0
% 3.61/0.99  bin_hyper_res:                          0
% 3.61/0.99  prep_cycles:                            4
% 3.61/0.99  pred_elim_time:                         0.007
% 3.61/0.99  splitting_time:                         0.
% 3.61/0.99  sem_filter_time:                        0.
% 3.61/0.99  monotx_time:                            0.
% 3.61/0.99  subtype_inf_time:                       0.
% 3.61/0.99  
% 3.61/0.99  ------ Problem properties
% 3.61/0.99  
% 3.61/0.99  clauses:                                16
% 3.61/0.99  conjectures:                            4
% 3.61/0.99  epr:                                    2
% 3.61/0.99  horn:                                   16
% 3.61/0.99  ground:                                 4
% 3.61/0.99  unary:                                  6
% 3.61/0.99  binary:                                 0
% 3.61/0.99  lits:                                   46
% 3.61/0.99  lits_eq:                                7
% 3.61/0.99  fd_pure:                                0
% 3.61/0.99  fd_pseudo:                              0
% 3.61/0.99  fd_cond:                                0
% 3.61/0.99  fd_pseudo_cond:                         1
% 3.61/0.99  ac_symbols:                             0
% 3.61/0.99  
% 3.61/0.99  ------ Propositional Solver
% 3.61/0.99  
% 3.61/0.99  prop_solver_calls:                      29
% 3.61/0.99  prop_fast_solver_calls:                 1045
% 3.61/0.99  smt_solver_calls:                       0
% 3.61/0.99  smt_fast_solver_calls:                  0
% 3.61/0.99  prop_num_of_clauses:                    3945
% 3.61/0.99  prop_preprocess_simplified:             6962
% 3.61/0.99  prop_fo_subsumed:                       44
% 3.61/0.99  prop_solver_time:                       0.
% 3.61/0.99  smt_solver_time:                        0.
% 3.61/0.99  smt_fast_solver_time:                   0.
% 3.61/0.99  prop_fast_solver_time:                  0.
% 3.61/0.99  prop_unsat_core_time:                   0.
% 3.61/0.99  
% 3.61/0.99  ------ QBF
% 3.61/0.99  
% 3.61/0.99  qbf_q_res:                              0
% 3.61/0.99  qbf_num_tautologies:                    0
% 3.61/0.99  qbf_prep_cycles:                        0
% 3.61/0.99  
% 3.61/0.99  ------ BMC1
% 3.61/0.99  
% 3.61/0.99  bmc1_current_bound:                     -1
% 3.61/0.99  bmc1_last_solved_bound:                 -1
% 3.61/0.99  bmc1_unsat_core_size:                   -1
% 3.61/0.99  bmc1_unsat_core_parents_size:           -1
% 3.61/0.99  bmc1_merge_next_fun:                    0
% 3.61/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.61/0.99  
% 3.61/0.99  ------ Instantiation
% 3.61/0.99  
% 3.61/0.99  inst_num_of_clauses:                    986
% 3.61/0.99  inst_num_in_passive:                    347
% 3.61/0.99  inst_num_in_active:                     599
% 3.61/0.99  inst_num_in_unprocessed:                39
% 3.61/0.99  inst_num_of_loops:                      627
% 3.61/0.99  inst_num_of_learning_restarts:          0
% 3.61/0.99  inst_num_moves_active_passive:          25
% 3.61/0.99  inst_lit_activity:                      0
% 3.61/0.99  inst_lit_activity_moves:                1
% 3.61/0.99  inst_num_tautologies:                   0
% 3.61/0.99  inst_num_prop_implied:                  0
% 3.61/0.99  inst_num_existing_simplified:           0
% 3.61/0.99  inst_num_eq_res_simplified:             0
% 3.61/0.99  inst_num_child_elim:                    0
% 3.61/0.99  inst_num_of_dismatching_blockings:      174
% 3.61/0.99  inst_num_of_non_proper_insts:           686
% 3.61/0.99  inst_num_of_duplicates:                 0
% 3.61/0.99  inst_inst_num_from_inst_to_res:         0
% 3.61/0.99  inst_dismatching_checking_time:         0.
% 3.61/0.99  
% 3.61/0.99  ------ Resolution
% 3.61/0.99  
% 3.61/0.99  res_num_of_clauses:                     0
% 3.61/0.99  res_num_in_passive:                     0
% 3.61/0.99  res_num_in_active:                      0
% 3.61/0.99  res_num_of_loops:                       98
% 3.61/0.99  res_forward_subset_subsumed:            22
% 3.61/0.99  res_backward_subset_subsumed:           0
% 3.61/0.99  res_forward_subsumed:                   0
% 3.61/0.99  res_backward_subsumed:                  0
% 3.61/0.99  res_forward_subsumption_resolution:     4
% 3.61/0.99  res_backward_subsumption_resolution:    0
% 3.61/0.99  res_clause_to_clause_subsumption:       1354
% 3.61/0.99  res_orphan_elimination:                 0
% 3.61/0.99  res_tautology_del:                      45
% 3.61/0.99  res_num_eq_res_simplified:              0
% 3.61/0.99  res_num_sel_changes:                    0
% 3.61/0.99  res_moves_from_active_to_pass:          0
% 3.61/0.99  
% 3.61/0.99  ------ Superposition
% 3.61/0.99  
% 3.61/0.99  sup_time_total:                         0.
% 3.61/0.99  sup_time_generating:                    0.
% 3.61/0.99  sup_time_sim_full:                      0.
% 3.61/0.99  sup_time_sim_immed:                     0.
% 3.61/0.99  
% 3.61/0.99  sup_num_of_clauses:                     283
% 3.61/0.99  sup_num_in_active:                      90
% 3.61/0.99  sup_num_in_passive:                     193
% 3.61/0.99  sup_num_of_loops:                       124
% 3.61/0.99  sup_fw_superposition:                   215
% 3.61/0.99  sup_bw_superposition:                   153
% 3.61/0.99  sup_immediate_simplified:               97
% 3.61/0.99  sup_given_eliminated:                   0
% 3.61/0.99  comparisons_done:                       0
% 3.61/0.99  comparisons_avoided:                    0
% 3.61/0.99  
% 3.61/0.99  ------ Simplifications
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  sim_fw_subset_subsumed:                 10
% 3.61/0.99  sim_bw_subset_subsumed:                 5
% 3.61/0.99  sim_fw_subsumed:                        15
% 3.61/0.99  sim_bw_subsumed:                        0
% 3.61/0.99  sim_fw_subsumption_res:                 2
% 3.61/0.99  sim_bw_subsumption_res:                 0
% 3.61/0.99  sim_tautology_del:                      4
% 3.61/0.99  sim_eq_tautology_del:                   27
% 3.61/0.99  sim_eq_res_simp:                        1
% 3.61/0.99  sim_fw_demodulated:                     7
% 3.61/0.99  sim_bw_demodulated:                     38
% 3.61/0.99  sim_light_normalised:                   85
% 3.61/0.99  sim_joinable_taut:                      0
% 3.61/0.99  sim_joinable_simp:                      0
% 3.61/0.99  sim_ac_normalised:                      0
% 3.61/0.99  sim_smt_subsumption:                    0
% 3.61/0.99  
%------------------------------------------------------------------------------
