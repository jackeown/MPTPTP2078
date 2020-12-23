%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:20:07 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :  194 (2725 expanded)
%              Number of clauses        :  123 ( 800 expanded)
%              Number of leaves         :   17 ( 748 expanded)
%              Depth                    :   26
%              Number of atoms          :  665 (9102 expanded)
%              Number of equality atoms :  158 (1083 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v2_lattice3(k2_yellow_1(X0))
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
               => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( v2_lattice3(k2_yellow_1(X0))
         => ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
          & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
     => ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,sK2),k3_xboole_0(X1,sK2))
        & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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

fof(f43,plain,
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

fof(f46,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))
    & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    & v2_lattice3(k2_yellow_1(sK0))
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f45,f44,f43])).

fof(f74,plain,(
    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f12,axiom,(
    ! [X0] : g1_orders_2(X0,k1_yellow_1(X0)) = k2_yellow_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : g1_orders_2(X0,k1_yellow_1(X0)) = k2_yellow_1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f88,plain,(
    m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) ),
    inference(definition_unfolding,[],[f74,f60])).

fof(f73,plain,(
    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f89,plain,(
    m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) ),
    inference(definition_unfolding,[],[f73,f60])).

fof(f10,axiom,(
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

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) = k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3)
      | ~ v4_orders_2(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f72,plain,(
    v2_lattice3(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f90,plain,(
    v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(definition_unfolding,[],[f72,f60])).

fof(f14,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : v4_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f80,plain,(
    ! [X0] : v4_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f65,f60])).

fof(f66,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f79,plain,(
    ! [X0] : v5_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f66,f60])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f77,plain,(
    ! [X0] : l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f62,f60])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
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

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = X1
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f81,plain,(
    ! [X0] : v3_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f64,f60])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f84,plain,(
    ! [X0] :
      ( ~ v2_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f67,f60])).

fof(f71,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f16,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f69,f60,f60,f60])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
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

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | k12_lattice3(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f75,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f46])).

fof(f87,plain,(
    ~ r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),k1_setfam_1(k2_tarski(sK1,sK2))) ),
    inference(definition_unfolding,[],[f75,f60,f48])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1329,plain,
    ( m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1328,plain,
    ( m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,k11_lattice3(X1,X2,X0),X3) = k11_lattice3(X1,X2,k11_lattice3(X1,X0,X3)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_25,negated_conjecture,
    ( v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_560,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,X2,k11_lattice3(X1,X0,X3)) = k11_lattice3(X1,k11_lattice3(X1,X2,X0),X3)
    | g1_orders_2(sK0,k1_yellow_1(sK0)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_25])).

cnf(c_561,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ v4_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X2)) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1),X2) ),
    inference(unflattening,[status(thm)],[c_560])).

cnf(c_15,plain,
    ( v4_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_51,plain,
    ( v4_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_14,plain,
    ( v5_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_54,plain,
    ( v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_12,plain,
    ( l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_58,plain,
    ( l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_565,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X2)) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1),X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_561,c_51,c_54,c_58])).

cnf(c_566,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,X0),X1) ),
    inference(renaming,[status(thm)],[c_565])).

cnf(c_1327,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X2)) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1),X2)
    | m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_566])).

cnf(c_2937,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,X0),X1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1))
    | m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1328,c_1327])).

cnf(c_3585,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),X0) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,X0))
    | m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1329,c_2937])).

cnf(c_3618,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2)) ),
    inference(superposition,[status(thm)],[c_1329,c_3585])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1333,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1)) = iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3762,plain,
    ( m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2)),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) = iProver_top
    | m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
    | l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3618,c_1333])).

cnf(c_29,plain,
    ( m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_30,plain,
    ( m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_57,plain,
    ( l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_59,plain,
    ( l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_57])).

cnf(c_1592,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))
    | m1_subset_1(k11_lattice3(g1_orders_2(X1,k1_yellow_1(X1)),X2,X0),u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))
    | ~ l1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1904,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_1592])).

cnf(c_2120,plain,
    ( m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_1904])).

cnf(c_2121,plain,
    ( m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
    | l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2120])).

cnf(c_1955,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,sK2)),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_1592])).

cnf(c_2293,plain,
    ( ~ m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,sK2)),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_1955])).

cnf(c_3556,plain,
    ( ~ m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2)),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_2293])).

cnf(c_3557,plain,
    ( m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
    | m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2)),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) = iProver_top
    | m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
    | l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3556])).

cnf(c_7362,plain,
    ( m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2)),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3762,c_29,c_30,c_59,c_2121,c_3557])).

cnf(c_10,plain,
    ( ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k12_lattice3(X0,X1,X2) = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_536,plain,
    ( ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k12_lattice3(X0,X1,X2) = X1
    | g1_orders_2(sK0,k1_yellow_1(sK0)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_25])).

cnf(c_537,plain,
    ( ~ r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_536])).

cnf(c_16,plain,
    ( v3_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_48,plain,
    ( v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_541,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_537,c_48,c_54,c_58])).

cnf(c_542,plain,
    ( ~ r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) = X0 ),
    inference(renaming,[status(thm)],[c_541])).

cnf(c_5,plain,
    ( r3_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_19,plain,
    ( v1_xboole_0(X0)
    | ~ v2_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_26,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_412,plain,
    ( ~ v2_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_26])).

cnf(c_413,plain,
    ( ~ v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(unflattening,[status(thm)],[c_412])).

cnf(c_431,plain,
    ( r3_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | g1_orders_2(sK0,k1_yellow_1(sK0)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_413])).

cnf(c_432,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(unflattening,[status(thm)],[c_431])).

cnf(c_436,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_432,c_48,c_58])).

cnf(c_437,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X0)
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) ),
    inference(renaming,[status(thm)],[c_436])).

cnf(c_722,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | X1 != X0
    | X1 != X2
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,X0) = X2
    | g1_orders_2(sK0,k1_yellow_1(sK0)) != g1_orders_2(sK0,k1_yellow_1(sK0)) ),
    inference(resolution_lifted,[status(thm)],[c_542,c_437])).

cnf(c_723,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_722])).

cnf(c_940,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X0) = X0
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_723])).

cnf(c_1321,plain,
    ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X0) = X0
    | m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_940])).

cnf(c_941,plain,
    ( sP2_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_723])).

cnf(c_978,plain,
    ( sP2_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_941])).

cnf(c_979,plain,
    ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X0) = X0
    | m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_940])).

cnf(c_21,plain,
    ( ~ r3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
    | r1_tarski(X1,X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_376,plain,
    ( ~ r3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
    | r1_tarski(X1,X2)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_26])).

cnf(c_377,plain,
    ( ~ r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | r1_tarski(X0,X1) ),
    inference(unflattening,[status(thm)],[c_376])).

cnf(c_737,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | r1_tarski(X2,X0)
    | X1 != X0
    | X1 != X2
    | g1_orders_2(sK0,k1_yellow_1(sK0)) != g1_orders_2(sK0,k1_yellow_1(sK0)) ),
    inference(resolution_lifted,[status(thm)],[c_377,c_437])).

cnf(c_738,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | r1_tarski(X0,X0) ),
    inference(unflattening,[status(thm)],[c_737])).

cnf(c_937,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_738])).

cnf(c_1319,plain,
    ( m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_937])).

cnf(c_2285,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1329,c_1319])).

cnf(c_3697,plain,
    ( m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1321,c_978,c_979,c_2285])).

cnf(c_3698,plain,
    ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X0) = X0
    | m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3697])).

cnf(c_3704,plain,
    ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_1329,c_3698])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_605,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0)
    | g1_orders_2(sK0,k1_yellow_1(sK0)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_25])).

cnf(c_606,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) ),
    inference(unflattening,[status(thm)],[c_605])).

cnf(c_610,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_606,c_54,c_58])).

cnf(c_611,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0) ),
    inference(renaming,[status(thm)],[c_610])).

cnf(c_1325,plain,
    ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)
    | m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_611])).

cnf(c_1566,plain,
    ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,X0) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,X0)
    | m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1329,c_1325])).

cnf(c_1610,plain,
    ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2) ),
    inference(superposition,[status(thm)],[c_1329,c_1566])).

cnf(c_3722,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_3704,c_1610])).

cnf(c_7366,plain,
    ( m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7362,c_3722])).

cnf(c_7402,plain,
    ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),X0) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),X0)
    | m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7366,c_1325])).

cnf(c_7578,plain,
    ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) ),
    inference(superposition,[status(thm)],[c_1329,c_7402])).

cnf(c_4365,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_3722,c_3618])).

cnf(c_7587,plain,
    ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_7578,c_4365])).

cnf(c_7579,plain,
    ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) ),
    inference(superposition,[status(thm)],[c_1328,c_7402])).

cnf(c_3619,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_1328,c_3585])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,X0,X2) = k11_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_584,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,X0,X2) = k11_lattice3(X1,X2,X0)
    | g1_orders_2(sK0,k1_yellow_1(sK0)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_25])).

cnf(c_585,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) ),
    inference(unflattening,[status(thm)],[c_584])).

cnf(c_589,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_585,c_54,c_58])).

cnf(c_590,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0) ),
    inference(renaming,[status(thm)],[c_589])).

cnf(c_1326,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0)
    | m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_590])).

cnf(c_2211,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,X0)
    | m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1329,c_1326])).

cnf(c_2272,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1328,c_2211])).

cnf(c_3621,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2)) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) ),
    inference(light_normalisation,[status(thm)],[c_3619,c_2272])).

cnf(c_3705,plain,
    ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_1328,c_3698])).

cnf(c_1567,plain,
    ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,X0) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,X0)
    | m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1328,c_1325])).

cnf(c_1642,plain,
    ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1) ),
    inference(superposition,[status(thm)],[c_1328,c_1567])).

cnf(c_3760,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_3705,c_1642])).

cnf(c_3586,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1),X0) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,X0))
    | m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1328,c_2937])).

cnf(c_3951,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1),sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1329,c_3586])).

cnf(c_5122,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2)) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_3760,c_3951])).

cnf(c_6641,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_3621,c_5122])).

cnf(c_7584,plain,
    ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_7579,c_6641])).

cnf(c_11,plain,
    ( r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k12_lattice3(X0,X1,X2) != X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_516,plain,
    ( r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k12_lattice3(X0,X1,X2) != X1
    | g1_orders_2(sK0,k1_yellow_1(sK0)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_25])).

cnf(c_517,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) != X0 ),
    inference(unflattening,[status(thm)],[c_516])).

cnf(c_519,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_517,c_48,c_54,c_58])).

cnf(c_520,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) != X0 ),
    inference(renaming,[status(thm)],[c_519])).

cnf(c_687,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | r1_tarski(X0,X1)
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) != X0 ),
    inference(resolution,[status(thm)],[c_520,c_377])).

cnf(c_1965,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,sK2),X0)
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,sK2),X0) != k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,sK2) ),
    inference(instantiation,[status(thm)],[c_687])).

cnf(c_2429,plain,
    ( ~ m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,sK2),sK1)
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,sK2),sK1) != k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,sK2) ),
    inference(instantiation,[status(thm)],[c_1965])).

cnf(c_3782,plain,
    ( ~ m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1)
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) != k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2429])).

cnf(c_2424,plain,
    ( ~ m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,sK2),sK2)
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,sK2),sK2) != k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,sK2) ),
    inference(instantiation,[status(thm)],[c_1965])).

cnf(c_3756,plain,
    ( ~ m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2)
    | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) != k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2424])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1338,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k1_setfam_1(k2_tarski(X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_22,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),k1_setfam_1(k2_tarski(sK1,sK2))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1330,plain,
    ( r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),k1_setfam_1(k2_tarski(sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2458,plain,
    ( r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) != iProver_top
    | r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1338,c_1330])).

cnf(c_2459,plain,
    ( ~ r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2)
    | ~ r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2458])).

cnf(c_2123,plain,
    ( m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_1904])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7587,c_7584,c_3782,c_3756,c_2459,c_2123,c_58,c_23,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:45:10 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.50/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/0.98  
% 3.50/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.50/0.98  
% 3.50/0.98  ------  iProver source info
% 3.50/0.98  
% 3.50/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.50/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.50/0.98  git: non_committed_changes: false
% 3.50/0.98  git: last_make_outside_of_git: false
% 3.50/0.98  
% 3.50/0.98  ------ 
% 3.50/0.98  
% 3.50/0.98  ------ Input Options
% 3.50/0.98  
% 3.50/0.98  --out_options                           all
% 3.50/0.98  --tptp_safe_out                         true
% 3.50/0.98  --problem_path                          ""
% 3.50/0.98  --include_path                          ""
% 3.50/0.98  --clausifier                            res/vclausify_rel
% 3.50/0.98  --clausifier_options                    --mode clausify
% 3.50/0.98  --stdin                                 false
% 3.50/0.98  --stats_out                             all
% 3.50/0.98  
% 3.50/0.98  ------ General Options
% 3.50/0.98  
% 3.50/0.98  --fof                                   false
% 3.50/0.98  --time_out_real                         305.
% 3.50/0.98  --time_out_virtual                      -1.
% 3.50/0.98  --symbol_type_check                     false
% 3.50/0.98  --clausify_out                          false
% 3.50/0.98  --sig_cnt_out                           false
% 3.50/0.98  --trig_cnt_out                          false
% 3.50/0.98  --trig_cnt_out_tolerance                1.
% 3.50/0.98  --trig_cnt_out_sk_spl                   false
% 3.50/0.98  --abstr_cl_out                          false
% 3.50/0.98  
% 3.50/0.98  ------ Global Options
% 3.50/0.98  
% 3.50/0.98  --schedule                              default
% 3.50/0.98  --add_important_lit                     false
% 3.50/0.98  --prop_solver_per_cl                    1000
% 3.50/0.98  --min_unsat_core                        false
% 3.50/0.98  --soft_assumptions                      false
% 3.50/0.98  --soft_lemma_size                       3
% 3.50/0.98  --prop_impl_unit_size                   0
% 3.50/0.98  --prop_impl_unit                        []
% 3.50/0.98  --share_sel_clauses                     true
% 3.50/0.98  --reset_solvers                         false
% 3.50/0.98  --bc_imp_inh                            [conj_cone]
% 3.50/0.98  --conj_cone_tolerance                   3.
% 3.50/0.98  --extra_neg_conj                        none
% 3.50/0.98  --large_theory_mode                     true
% 3.50/0.98  --prolific_symb_bound                   200
% 3.50/0.98  --lt_threshold                          2000
% 3.50/0.98  --clause_weak_htbl                      true
% 3.50/0.98  --gc_record_bc_elim                     false
% 3.50/0.98  
% 3.50/0.98  ------ Preprocessing Options
% 3.50/0.98  
% 3.50/0.98  --preprocessing_flag                    true
% 3.50/0.98  --time_out_prep_mult                    0.1
% 3.50/0.98  --splitting_mode                        input
% 3.50/0.98  --splitting_grd                         true
% 3.50/0.98  --splitting_cvd                         false
% 3.50/0.98  --splitting_cvd_svl                     false
% 3.50/0.98  --splitting_nvd                         32
% 3.50/0.98  --sub_typing                            true
% 3.50/0.98  --prep_gs_sim                           true
% 3.50/0.98  --prep_unflatten                        true
% 3.50/0.98  --prep_res_sim                          true
% 3.50/0.98  --prep_upred                            true
% 3.50/0.98  --prep_sem_filter                       exhaustive
% 3.50/0.98  --prep_sem_filter_out                   false
% 3.50/0.98  --pred_elim                             true
% 3.50/0.98  --res_sim_input                         true
% 3.50/0.98  --eq_ax_congr_red                       true
% 3.50/0.98  --pure_diseq_elim                       true
% 3.50/0.98  --brand_transform                       false
% 3.50/0.98  --non_eq_to_eq                          false
% 3.50/0.98  --prep_def_merge                        true
% 3.50/0.98  --prep_def_merge_prop_impl              false
% 3.50/0.98  --prep_def_merge_mbd                    true
% 3.50/0.98  --prep_def_merge_tr_red                 false
% 3.50/0.98  --prep_def_merge_tr_cl                  false
% 3.50/0.98  --smt_preprocessing                     true
% 3.50/0.98  --smt_ac_axioms                         fast
% 3.50/0.98  --preprocessed_out                      false
% 3.50/0.98  --preprocessed_stats                    false
% 3.50/0.98  
% 3.50/0.98  ------ Abstraction refinement Options
% 3.50/0.98  
% 3.50/0.98  --abstr_ref                             []
% 3.50/0.98  --abstr_ref_prep                        false
% 3.50/0.98  --abstr_ref_until_sat                   false
% 3.50/0.98  --abstr_ref_sig_restrict                funpre
% 3.50/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.50/0.98  --abstr_ref_under                       []
% 3.50/0.98  
% 3.50/0.98  ------ SAT Options
% 3.50/0.98  
% 3.50/0.98  --sat_mode                              false
% 3.50/0.98  --sat_fm_restart_options                ""
% 3.50/0.98  --sat_gr_def                            false
% 3.50/0.98  --sat_epr_types                         true
% 3.50/0.98  --sat_non_cyclic_types                  false
% 3.50/0.98  --sat_finite_models                     false
% 3.50/0.98  --sat_fm_lemmas                         false
% 3.50/0.98  --sat_fm_prep                           false
% 3.50/0.99  --sat_fm_uc_incr                        true
% 3.50/0.99  --sat_out_model                         small
% 3.50/0.99  --sat_out_clauses                       false
% 3.50/0.99  
% 3.50/0.99  ------ QBF Options
% 3.50/0.99  
% 3.50/0.99  --qbf_mode                              false
% 3.50/0.99  --qbf_elim_univ                         false
% 3.50/0.99  --qbf_dom_inst                          none
% 3.50/0.99  --qbf_dom_pre_inst                      false
% 3.50/0.99  --qbf_sk_in                             false
% 3.50/0.99  --qbf_pred_elim                         true
% 3.50/0.99  --qbf_split                             512
% 3.50/0.99  
% 3.50/0.99  ------ BMC1 Options
% 3.50/0.99  
% 3.50/0.99  --bmc1_incremental                      false
% 3.50/0.99  --bmc1_axioms                           reachable_all
% 3.50/0.99  --bmc1_min_bound                        0
% 3.50/0.99  --bmc1_max_bound                        -1
% 3.50/0.99  --bmc1_max_bound_default                -1
% 3.50/0.99  --bmc1_symbol_reachability              true
% 3.50/0.99  --bmc1_property_lemmas                  false
% 3.50/0.99  --bmc1_k_induction                      false
% 3.50/0.99  --bmc1_non_equiv_states                 false
% 3.50/0.99  --bmc1_deadlock                         false
% 3.50/0.99  --bmc1_ucm                              false
% 3.50/0.99  --bmc1_add_unsat_core                   none
% 3.50/0.99  --bmc1_unsat_core_children              false
% 3.50/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.50/0.99  --bmc1_out_stat                         full
% 3.50/0.99  --bmc1_ground_init                      false
% 3.50/0.99  --bmc1_pre_inst_next_state              false
% 3.50/0.99  --bmc1_pre_inst_state                   false
% 3.50/0.99  --bmc1_pre_inst_reach_state             false
% 3.50/0.99  --bmc1_out_unsat_core                   false
% 3.50/0.99  --bmc1_aig_witness_out                  false
% 3.50/0.99  --bmc1_verbose                          false
% 3.50/0.99  --bmc1_dump_clauses_tptp                false
% 3.50/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.50/0.99  --bmc1_dump_file                        -
% 3.50/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.50/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.50/0.99  --bmc1_ucm_extend_mode                  1
% 3.50/0.99  --bmc1_ucm_init_mode                    2
% 3.50/0.99  --bmc1_ucm_cone_mode                    none
% 3.50/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.50/0.99  --bmc1_ucm_relax_model                  4
% 3.50/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.50/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.50/0.99  --bmc1_ucm_layered_model                none
% 3.50/0.99  --bmc1_ucm_max_lemma_size               10
% 3.50/0.99  
% 3.50/0.99  ------ AIG Options
% 3.50/0.99  
% 3.50/0.99  --aig_mode                              false
% 3.50/0.99  
% 3.50/0.99  ------ Instantiation Options
% 3.50/0.99  
% 3.50/0.99  --instantiation_flag                    true
% 3.50/0.99  --inst_sos_flag                         false
% 3.50/0.99  --inst_sos_phase                        true
% 3.50/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.50/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.50/0.99  --inst_lit_sel_side                     num_symb
% 3.50/0.99  --inst_solver_per_active                1400
% 3.50/0.99  --inst_solver_calls_frac                1.
% 3.50/0.99  --inst_passive_queue_type               priority_queues
% 3.50/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.50/0.99  --inst_passive_queues_freq              [25;2]
% 3.50/0.99  --inst_dismatching                      true
% 3.50/0.99  --inst_eager_unprocessed_to_passive     true
% 3.50/0.99  --inst_prop_sim_given                   true
% 3.50/0.99  --inst_prop_sim_new                     false
% 3.50/0.99  --inst_subs_new                         false
% 3.50/0.99  --inst_eq_res_simp                      false
% 3.50/0.99  --inst_subs_given                       false
% 3.50/0.99  --inst_orphan_elimination               true
% 3.50/0.99  --inst_learning_loop_flag               true
% 3.50/0.99  --inst_learning_start                   3000
% 3.50/0.99  --inst_learning_factor                  2
% 3.50/0.99  --inst_start_prop_sim_after_learn       3
% 3.50/0.99  --inst_sel_renew                        solver
% 3.50/0.99  --inst_lit_activity_flag                true
% 3.50/0.99  --inst_restr_to_given                   false
% 3.50/0.99  --inst_activity_threshold               500
% 3.50/0.99  --inst_out_proof                        true
% 3.50/0.99  
% 3.50/0.99  ------ Resolution Options
% 3.50/0.99  
% 3.50/0.99  --resolution_flag                       true
% 3.50/0.99  --res_lit_sel                           adaptive
% 3.50/0.99  --res_lit_sel_side                      none
% 3.50/0.99  --res_ordering                          kbo
% 3.50/0.99  --res_to_prop_solver                    active
% 3.50/0.99  --res_prop_simpl_new                    false
% 3.50/0.99  --res_prop_simpl_given                  true
% 3.50/0.99  --res_passive_queue_type                priority_queues
% 3.50/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.50/0.99  --res_passive_queues_freq               [15;5]
% 3.50/0.99  --res_forward_subs                      full
% 3.50/0.99  --res_backward_subs                     full
% 3.50/0.99  --res_forward_subs_resolution           true
% 3.50/0.99  --res_backward_subs_resolution          true
% 3.50/0.99  --res_orphan_elimination                true
% 3.50/0.99  --res_time_limit                        2.
% 3.50/0.99  --res_out_proof                         true
% 3.50/0.99  
% 3.50/0.99  ------ Superposition Options
% 3.50/0.99  
% 3.50/0.99  --superposition_flag                    true
% 3.50/0.99  --sup_passive_queue_type                priority_queues
% 3.50/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.50/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.50/0.99  --demod_completeness_check              fast
% 3.50/0.99  --demod_use_ground                      true
% 3.50/0.99  --sup_to_prop_solver                    passive
% 3.50/0.99  --sup_prop_simpl_new                    true
% 3.50/0.99  --sup_prop_simpl_given                  true
% 3.50/0.99  --sup_fun_splitting                     false
% 3.50/0.99  --sup_smt_interval                      50000
% 3.50/0.99  
% 3.50/0.99  ------ Superposition Simplification Setup
% 3.50/0.99  
% 3.50/0.99  --sup_indices_passive                   []
% 3.50/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.50/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.99  --sup_full_bw                           [BwDemod]
% 3.50/0.99  --sup_immed_triv                        [TrivRules]
% 3.50/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.50/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.99  --sup_immed_bw_main                     []
% 3.50/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.50/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/0.99  
% 3.50/0.99  ------ Combination Options
% 3.50/0.99  
% 3.50/0.99  --comb_res_mult                         3
% 3.50/0.99  --comb_sup_mult                         2
% 3.50/0.99  --comb_inst_mult                        10
% 3.50/0.99  
% 3.50/0.99  ------ Debug Options
% 3.50/0.99  
% 3.50/0.99  --dbg_backtrace                         false
% 3.50/0.99  --dbg_dump_prop_clauses                 false
% 3.50/0.99  --dbg_dump_prop_clauses_file            -
% 3.50/0.99  --dbg_out_stat                          false
% 3.50/0.99  ------ Parsing...
% 3.50/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.50/0.99  
% 3.50/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 3.50/0.99  
% 3.50/0.99  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.50/0.99  
% 3.50/0.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.50/0.99  ------ Proving...
% 3.50/0.99  ------ Problem Properties 
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  clauses                                 22
% 3.50/0.99  conjectures                             3
% 3.50/0.99  EPR                                     2
% 3.50/0.99  Horn                                    20
% 3.50/0.99  unary                                   5
% 3.50/0.99  binary                                  5
% 3.50/0.99  lits                                    55
% 3.50/0.99  lits eq                                 11
% 3.50/0.99  fd_pure                                 0
% 3.50/0.99  fd_pseudo                               0
% 3.50/0.99  fd_cond                                 0
% 3.50/0.99  fd_pseudo_cond                          2
% 3.50/0.99  AC symbols                              0
% 3.50/0.99  
% 3.50/0.99  ------ Schedule dynamic 5 is on 
% 3.50/0.99  
% 3.50/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  ------ 
% 3.50/0.99  Current options:
% 3.50/0.99  ------ 
% 3.50/0.99  
% 3.50/0.99  ------ Input Options
% 3.50/0.99  
% 3.50/0.99  --out_options                           all
% 3.50/0.99  --tptp_safe_out                         true
% 3.50/0.99  --problem_path                          ""
% 3.50/0.99  --include_path                          ""
% 3.50/0.99  --clausifier                            res/vclausify_rel
% 3.50/0.99  --clausifier_options                    --mode clausify
% 3.50/0.99  --stdin                                 false
% 3.50/0.99  --stats_out                             all
% 3.50/0.99  
% 3.50/0.99  ------ General Options
% 3.50/0.99  
% 3.50/0.99  --fof                                   false
% 3.50/0.99  --time_out_real                         305.
% 3.50/0.99  --time_out_virtual                      -1.
% 3.50/0.99  --symbol_type_check                     false
% 3.50/0.99  --clausify_out                          false
% 3.50/0.99  --sig_cnt_out                           false
% 3.50/0.99  --trig_cnt_out                          false
% 3.50/0.99  --trig_cnt_out_tolerance                1.
% 3.50/0.99  --trig_cnt_out_sk_spl                   false
% 3.50/0.99  --abstr_cl_out                          false
% 3.50/0.99  
% 3.50/0.99  ------ Global Options
% 3.50/0.99  
% 3.50/0.99  --schedule                              default
% 3.50/0.99  --add_important_lit                     false
% 3.50/0.99  --prop_solver_per_cl                    1000
% 3.50/0.99  --min_unsat_core                        false
% 3.50/0.99  --soft_assumptions                      false
% 3.50/0.99  --soft_lemma_size                       3
% 3.50/0.99  --prop_impl_unit_size                   0
% 3.50/0.99  --prop_impl_unit                        []
% 3.50/0.99  --share_sel_clauses                     true
% 3.50/0.99  --reset_solvers                         false
% 3.50/0.99  --bc_imp_inh                            [conj_cone]
% 3.50/0.99  --conj_cone_tolerance                   3.
% 3.50/0.99  --extra_neg_conj                        none
% 3.50/0.99  --large_theory_mode                     true
% 3.50/0.99  --prolific_symb_bound                   200
% 3.50/0.99  --lt_threshold                          2000
% 3.50/0.99  --clause_weak_htbl                      true
% 3.50/0.99  --gc_record_bc_elim                     false
% 3.50/0.99  
% 3.50/0.99  ------ Preprocessing Options
% 3.50/0.99  
% 3.50/0.99  --preprocessing_flag                    true
% 3.50/0.99  --time_out_prep_mult                    0.1
% 3.50/0.99  --splitting_mode                        input
% 3.50/0.99  --splitting_grd                         true
% 3.50/0.99  --splitting_cvd                         false
% 3.50/0.99  --splitting_cvd_svl                     false
% 3.50/0.99  --splitting_nvd                         32
% 3.50/0.99  --sub_typing                            true
% 3.50/0.99  --prep_gs_sim                           true
% 3.50/0.99  --prep_unflatten                        true
% 3.50/0.99  --prep_res_sim                          true
% 3.50/0.99  --prep_upred                            true
% 3.50/0.99  --prep_sem_filter                       exhaustive
% 3.50/0.99  --prep_sem_filter_out                   false
% 3.50/0.99  --pred_elim                             true
% 3.50/0.99  --res_sim_input                         true
% 3.50/0.99  --eq_ax_congr_red                       true
% 3.50/0.99  --pure_diseq_elim                       true
% 3.50/0.99  --brand_transform                       false
% 3.50/0.99  --non_eq_to_eq                          false
% 3.50/0.99  --prep_def_merge                        true
% 3.50/0.99  --prep_def_merge_prop_impl              false
% 3.50/0.99  --prep_def_merge_mbd                    true
% 3.50/0.99  --prep_def_merge_tr_red                 false
% 3.50/0.99  --prep_def_merge_tr_cl                  false
% 3.50/0.99  --smt_preprocessing                     true
% 3.50/0.99  --smt_ac_axioms                         fast
% 3.50/0.99  --preprocessed_out                      false
% 3.50/0.99  --preprocessed_stats                    false
% 3.50/0.99  
% 3.50/0.99  ------ Abstraction refinement Options
% 3.50/0.99  
% 3.50/0.99  --abstr_ref                             []
% 3.50/0.99  --abstr_ref_prep                        false
% 3.50/0.99  --abstr_ref_until_sat                   false
% 3.50/0.99  --abstr_ref_sig_restrict                funpre
% 3.50/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.50/0.99  --abstr_ref_under                       []
% 3.50/0.99  
% 3.50/0.99  ------ SAT Options
% 3.50/0.99  
% 3.50/0.99  --sat_mode                              false
% 3.50/0.99  --sat_fm_restart_options                ""
% 3.50/0.99  --sat_gr_def                            false
% 3.50/0.99  --sat_epr_types                         true
% 3.50/0.99  --sat_non_cyclic_types                  false
% 3.50/0.99  --sat_finite_models                     false
% 3.50/0.99  --sat_fm_lemmas                         false
% 3.50/0.99  --sat_fm_prep                           false
% 3.50/0.99  --sat_fm_uc_incr                        true
% 3.50/0.99  --sat_out_model                         small
% 3.50/0.99  --sat_out_clauses                       false
% 3.50/0.99  
% 3.50/0.99  ------ QBF Options
% 3.50/0.99  
% 3.50/0.99  --qbf_mode                              false
% 3.50/0.99  --qbf_elim_univ                         false
% 3.50/0.99  --qbf_dom_inst                          none
% 3.50/0.99  --qbf_dom_pre_inst                      false
% 3.50/0.99  --qbf_sk_in                             false
% 3.50/0.99  --qbf_pred_elim                         true
% 3.50/0.99  --qbf_split                             512
% 3.50/0.99  
% 3.50/0.99  ------ BMC1 Options
% 3.50/0.99  
% 3.50/0.99  --bmc1_incremental                      false
% 3.50/0.99  --bmc1_axioms                           reachable_all
% 3.50/0.99  --bmc1_min_bound                        0
% 3.50/0.99  --bmc1_max_bound                        -1
% 3.50/0.99  --bmc1_max_bound_default                -1
% 3.50/0.99  --bmc1_symbol_reachability              true
% 3.50/0.99  --bmc1_property_lemmas                  false
% 3.50/0.99  --bmc1_k_induction                      false
% 3.50/0.99  --bmc1_non_equiv_states                 false
% 3.50/0.99  --bmc1_deadlock                         false
% 3.50/0.99  --bmc1_ucm                              false
% 3.50/0.99  --bmc1_add_unsat_core                   none
% 3.50/0.99  --bmc1_unsat_core_children              false
% 3.50/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.50/0.99  --bmc1_out_stat                         full
% 3.50/0.99  --bmc1_ground_init                      false
% 3.50/0.99  --bmc1_pre_inst_next_state              false
% 3.50/0.99  --bmc1_pre_inst_state                   false
% 3.50/0.99  --bmc1_pre_inst_reach_state             false
% 3.50/0.99  --bmc1_out_unsat_core                   false
% 3.50/0.99  --bmc1_aig_witness_out                  false
% 3.50/0.99  --bmc1_verbose                          false
% 3.50/0.99  --bmc1_dump_clauses_tptp                false
% 3.50/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.50/0.99  --bmc1_dump_file                        -
% 3.50/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.50/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.50/0.99  --bmc1_ucm_extend_mode                  1
% 3.50/0.99  --bmc1_ucm_init_mode                    2
% 3.50/0.99  --bmc1_ucm_cone_mode                    none
% 3.50/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.50/0.99  --bmc1_ucm_relax_model                  4
% 3.50/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.50/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.50/0.99  --bmc1_ucm_layered_model                none
% 3.50/0.99  --bmc1_ucm_max_lemma_size               10
% 3.50/0.99  
% 3.50/0.99  ------ AIG Options
% 3.50/0.99  
% 3.50/0.99  --aig_mode                              false
% 3.50/0.99  
% 3.50/0.99  ------ Instantiation Options
% 3.50/0.99  
% 3.50/0.99  --instantiation_flag                    true
% 3.50/0.99  --inst_sos_flag                         false
% 3.50/0.99  --inst_sos_phase                        true
% 3.50/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.50/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.50/0.99  --inst_lit_sel_side                     none
% 3.50/0.99  --inst_solver_per_active                1400
% 3.50/0.99  --inst_solver_calls_frac                1.
% 3.50/0.99  --inst_passive_queue_type               priority_queues
% 3.50/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.50/0.99  --inst_passive_queues_freq              [25;2]
% 3.50/0.99  --inst_dismatching                      true
% 3.50/0.99  --inst_eager_unprocessed_to_passive     true
% 3.50/0.99  --inst_prop_sim_given                   true
% 3.50/0.99  --inst_prop_sim_new                     false
% 3.50/0.99  --inst_subs_new                         false
% 3.50/0.99  --inst_eq_res_simp                      false
% 3.50/0.99  --inst_subs_given                       false
% 3.50/0.99  --inst_orphan_elimination               true
% 3.50/0.99  --inst_learning_loop_flag               true
% 3.50/0.99  --inst_learning_start                   3000
% 3.50/0.99  --inst_learning_factor                  2
% 3.50/0.99  --inst_start_prop_sim_after_learn       3
% 3.50/0.99  --inst_sel_renew                        solver
% 3.50/0.99  --inst_lit_activity_flag                true
% 3.50/0.99  --inst_restr_to_given                   false
% 3.50/0.99  --inst_activity_threshold               500
% 3.50/0.99  --inst_out_proof                        true
% 3.50/0.99  
% 3.50/0.99  ------ Resolution Options
% 3.50/0.99  
% 3.50/0.99  --resolution_flag                       false
% 3.50/0.99  --res_lit_sel                           adaptive
% 3.50/0.99  --res_lit_sel_side                      none
% 3.50/0.99  --res_ordering                          kbo
% 3.50/0.99  --res_to_prop_solver                    active
% 3.50/0.99  --res_prop_simpl_new                    false
% 3.50/0.99  --res_prop_simpl_given                  true
% 3.50/0.99  --res_passive_queue_type                priority_queues
% 3.50/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.50/0.99  --res_passive_queues_freq               [15;5]
% 3.50/0.99  --res_forward_subs                      full
% 3.50/0.99  --res_backward_subs                     full
% 3.50/0.99  --res_forward_subs_resolution           true
% 3.50/0.99  --res_backward_subs_resolution          true
% 3.50/0.99  --res_orphan_elimination                true
% 3.50/0.99  --res_time_limit                        2.
% 3.50/0.99  --res_out_proof                         true
% 3.50/0.99  
% 3.50/0.99  ------ Superposition Options
% 3.50/0.99  
% 3.50/0.99  --superposition_flag                    true
% 3.50/0.99  --sup_passive_queue_type                priority_queues
% 3.50/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.50/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.50/0.99  --demod_completeness_check              fast
% 3.50/0.99  --demod_use_ground                      true
% 3.50/0.99  --sup_to_prop_solver                    passive
% 3.50/0.99  --sup_prop_simpl_new                    true
% 3.50/0.99  --sup_prop_simpl_given                  true
% 3.50/0.99  --sup_fun_splitting                     false
% 3.50/0.99  --sup_smt_interval                      50000
% 3.50/0.99  
% 3.50/0.99  ------ Superposition Simplification Setup
% 3.50/0.99  
% 3.50/0.99  --sup_indices_passive                   []
% 3.50/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.50/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.99  --sup_full_bw                           [BwDemod]
% 3.50/0.99  --sup_immed_triv                        [TrivRules]
% 3.50/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.50/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.99  --sup_immed_bw_main                     []
% 3.50/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.50/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/0.99  
% 3.50/0.99  ------ Combination Options
% 3.50/0.99  
% 3.50/0.99  --comb_res_mult                         3
% 3.50/0.99  --comb_sup_mult                         2
% 3.50/0.99  --comb_inst_mult                        10
% 3.50/0.99  
% 3.50/0.99  ------ Debug Options
% 3.50/0.99  
% 3.50/0.99  --dbg_backtrace                         false
% 3.50/0.99  --dbg_dump_prop_clauses                 false
% 3.50/0.99  --dbg_dump_prop_clauses_file            -
% 3.50/0.99  --dbg_out_stat                          false
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  ------ Proving...
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  % SZS status Theorem for theBenchmark.p
% 3.50/0.99  
% 3.50/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.50/0.99  
% 3.50/0.99  fof(f17,conjecture,(
% 3.50/0.99    ! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f18,negated_conjecture,(
% 3.50/0.99    ~! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 3.50/0.99    inference(negated_conjecture,[],[f17])).
% 3.50/0.99  
% 3.50/0.99  fof(f39,plain,(
% 3.50/0.99    ? [X0] : ((? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0))) & ~v1_xboole_0(X0))),
% 3.50/0.99    inference(ennf_transformation,[],[f18])).
% 3.50/0.99  
% 3.50/0.99  fof(f40,plain,(
% 3.50/0.99    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0))),
% 3.50/0.99    inference(flattening,[],[f39])).
% 3.50/0.99  
% 3.50/0.99  fof(f45,plain,(
% 3.50/0.99    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) => (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,sK2),k3_xboole_0(X1,sK2)) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(X0))))) )),
% 3.50/0.99    introduced(choice_axiom,[])).
% 3.50/0.99  
% 3.50/0.99  fof(f44,plain,(
% 3.50/0.99    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) => (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),sK1,X2),k3_xboole_0(sK1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(X0))))) )),
% 3.50/0.99    introduced(choice_axiom,[])).
% 3.50/0.99  
% 3.50/0.99  fof(f43,plain,(
% 3.50/0.99    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) & v2_lattice3(k2_yellow_1(sK0)) & ~v1_xboole_0(sK0))),
% 3.50/0.99    introduced(choice_axiom,[])).
% 3.50/0.99  
% 3.50/0.99  fof(f46,plain,(
% 3.50/0.99    ((~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))) & v2_lattice3(k2_yellow_1(sK0)) & ~v1_xboole_0(sK0)),
% 3.50/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f45,f44,f43])).
% 3.50/0.99  
% 3.50/0.99  fof(f74,plain,(
% 3.50/0.99    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 3.50/0.99    inference(cnf_transformation,[],[f46])).
% 3.50/0.99  
% 3.50/0.99  fof(f12,axiom,(
% 3.50/0.99    ! [X0] : g1_orders_2(X0,k1_yellow_1(X0)) = k2_yellow_1(X0)),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f60,plain,(
% 3.50/0.99    ( ! [X0] : (g1_orders_2(X0,k1_yellow_1(X0)) = k2_yellow_1(X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f12])).
% 3.50/0.99  
% 3.50/0.99  fof(f88,plain,(
% 3.50/0.99    m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))),
% 3.50/0.99    inference(definition_unfolding,[],[f74,f60])).
% 3.50/0.99  
% 3.50/0.99  fof(f73,plain,(
% 3.50/0.99    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 3.50/0.99    inference(cnf_transformation,[],[f46])).
% 3.50/0.99  
% 3.50/0.99  fof(f89,plain,(
% 3.50/0.99    m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))),
% 3.50/0.99    inference(definition_unfolding,[],[f73,f60])).
% 3.50/0.99  
% 3.50/0.99  fof(f10,axiom,(
% 3.50/0.99    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (v4_orders_2(X0) => k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) = k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3))))))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f33,plain,(
% 3.50/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) = k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) | ~v4_orders_2(X0)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 3.50/0.99    inference(ennf_transformation,[],[f10])).
% 3.50/0.99  
% 3.50/0.99  fof(f34,plain,(
% 3.50/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) = k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) | ~v4_orders_2(X0) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 3.50/0.99    inference(flattening,[],[f33])).
% 3.50/0.99  
% 3.50/0.99  fof(f57,plain,(
% 3.50/0.99    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) = k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) | ~v4_orders_2(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f34])).
% 3.50/0.99  
% 3.50/0.99  fof(f72,plain,(
% 3.50/0.99    v2_lattice3(k2_yellow_1(sK0))),
% 3.50/0.99    inference(cnf_transformation,[],[f46])).
% 3.50/0.99  
% 3.50/0.99  fof(f90,plain,(
% 3.50/0.99    v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))),
% 3.50/0.99    inference(definition_unfolding,[],[f72,f60])).
% 3.50/0.99  
% 3.50/0.99  fof(f14,axiom,(
% 3.50/0.99    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f65,plain,(
% 3.50/0.99    ( ! [X0] : (v4_orders_2(k2_yellow_1(X0))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f14])).
% 3.50/0.99  
% 3.50/0.99  fof(f80,plain,(
% 3.50/0.99    ( ! [X0] : (v4_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) )),
% 3.50/0.99    inference(definition_unfolding,[],[f65,f60])).
% 3.50/0.99  
% 3.50/0.99  fof(f66,plain,(
% 3.50/0.99    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f14])).
% 3.50/0.99  
% 3.50/0.99  fof(f79,plain,(
% 3.50/0.99    ( ! [X0] : (v5_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) )),
% 3.50/0.99    inference(definition_unfolding,[],[f66,f60])).
% 3.50/0.99  
% 3.50/0.99  fof(f13,axiom,(
% 3.50/0.99    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f62,plain,(
% 3.50/0.99    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f13])).
% 3.50/0.99  
% 3.50/0.99  fof(f77,plain,(
% 3.50/0.99    ( ! [X0] : (l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) )),
% 3.50/0.99    inference(definition_unfolding,[],[f62,f60])).
% 3.50/0.99  
% 3.50/0.99  fof(f7,axiom,(
% 3.50/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f27,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 3.50/0.99    inference(ennf_transformation,[],[f7])).
% 3.50/0.99  
% 3.50/0.99  fof(f28,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 3.50/0.99    inference(flattening,[],[f27])).
% 3.50/0.99  
% 3.50/0.99  fof(f54,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f28])).
% 3.50/0.99  
% 3.50/0.99  fof(f11,axiom,(
% 3.50/0.99    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k12_lattice3(X0,X1,X2) = X1 <=> r3_orders_2(X0,X1,X2)))))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f35,plain,(
% 3.50/0.99    ! [X0] : (! [X1] : (! [X2] : ((k12_lattice3(X0,X1,X2) = X1 <=> r3_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)))),
% 3.50/0.99    inference(ennf_transformation,[],[f11])).
% 3.50/0.99  
% 3.50/0.99  fof(f36,plain,(
% 3.50/0.99    ! [X0] : (! [X1] : (! [X2] : ((k12_lattice3(X0,X1,X2) = X1 <=> r3_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 3.50/0.99    inference(flattening,[],[f35])).
% 3.50/0.99  
% 3.50/0.99  fof(f41,plain,(
% 3.50/0.99    ! [X0] : (! [X1] : (! [X2] : (((k12_lattice3(X0,X1,X2) = X1 | ~r3_orders_2(X0,X1,X2)) & (r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) != X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 3.50/0.99    inference(nnf_transformation,[],[f36])).
% 3.50/0.99  
% 3.50/0.99  fof(f59,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (k12_lattice3(X0,X1,X2) = X1 | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f41])).
% 3.50/0.99  
% 3.50/0.99  fof(f64,plain,(
% 3.50/0.99    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f14])).
% 3.50/0.99  
% 3.50/0.99  fof(f81,plain,(
% 3.50/0.99    ( ! [X0] : (v3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) )),
% 3.50/0.99    inference(definition_unfolding,[],[f64,f60])).
% 3.50/0.99  
% 3.50/0.99  fof(f6,axiom,(
% 3.50/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => r3_orders_2(X0,X1,X1))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f25,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.50/0.99    inference(ennf_transformation,[],[f6])).
% 3.50/0.99  
% 3.50/0.99  fof(f26,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.50/0.99    inference(flattening,[],[f25])).
% 3.50/0.99  
% 3.50/0.99  fof(f53,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f26])).
% 3.50/0.99  
% 3.50/0.99  fof(f15,axiom,(
% 3.50/0.99    ! [X0] : (~v1_xboole_0(X0) => (v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f37,plain,(
% 3.50/0.99    ! [X0] : ((v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0))),
% 3.50/0.99    inference(ennf_transformation,[],[f15])).
% 3.50/0.99  
% 3.50/0.99  fof(f67,plain,(
% 3.50/0.99    ( ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f37])).
% 3.50/0.99  
% 3.50/0.99  fof(f84,plain,(
% 3.50/0.99    ( ! [X0] : (~v2_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 3.50/0.99    inference(definition_unfolding,[],[f67,f60])).
% 3.50/0.99  
% 3.50/0.99  fof(f71,plain,(
% 3.50/0.99    ~v1_xboole_0(sK0)),
% 3.50/0.99    inference(cnf_transformation,[],[f46])).
% 3.50/0.99  
% 3.50/0.99  fof(f16,axiom,(
% 3.50/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f38,plain,(
% 3.50/0.99    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 3.50/0.99    inference(ennf_transformation,[],[f16])).
% 3.50/0.99  
% 3.50/0.99  fof(f42,plain,(
% 3.50/0.99    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 3.50/0.99    inference(nnf_transformation,[],[f38])).
% 3.50/0.99  
% 3.50/0.99  fof(f69,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f42])).
% 3.50/0.99  
% 3.50/0.99  fof(f86,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2) | ~m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | v1_xboole_0(X0)) )),
% 3.50/0.99    inference(definition_unfolding,[],[f69,f60,f60,f60])).
% 3.50/0.99  
% 3.50/0.99  fof(f8,axiom,(
% 3.50/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f29,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 3.50/0.99    inference(ennf_transformation,[],[f8])).
% 3.50/0.99  
% 3.50/0.99  fof(f30,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 3.50/0.99    inference(flattening,[],[f29])).
% 3.50/0.99  
% 3.50/0.99  fof(f55,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f30])).
% 3.50/0.99  
% 3.50/0.99  fof(f9,axiom,(
% 3.50/0.99    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1))))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f31,plain,(
% 3.50/0.99    ! [X0] : (! [X1] : (! [X2] : (k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 3.50/0.99    inference(ennf_transformation,[],[f9])).
% 3.50/0.99  
% 3.50/0.99  fof(f32,plain,(
% 3.50/0.99    ! [X0] : (! [X1] : (! [X2] : (k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 3.50/0.99    inference(flattening,[],[f31])).
% 3.50/0.99  
% 3.50/0.99  fof(f56,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f32])).
% 3.50/0.99  
% 3.50/0.99  fof(f58,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) != X1 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f41])).
% 3.50/0.99  
% 3.50/0.99  fof(f1,axiom,(
% 3.50/0.99    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f19,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 3.50/0.99    inference(ennf_transformation,[],[f1])).
% 3.50/0.99  
% 3.50/0.99  fof(f20,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 3.50/0.99    inference(flattening,[],[f19])).
% 3.50/0.99  
% 3.50/0.99  fof(f47,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f20])).
% 3.50/0.99  
% 3.50/0.99  fof(f2,axiom,(
% 3.50/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f48,plain,(
% 3.50/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f2])).
% 3.50/0.99  
% 3.50/0.99  fof(f76,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.50/0.99    inference(definition_unfolding,[],[f47,f48])).
% 3.50/0.99  
% 3.50/0.99  fof(f75,plain,(
% 3.50/0.99    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))),
% 3.50/0.99    inference(cnf_transformation,[],[f46])).
% 3.50/0.99  
% 3.50/0.99  fof(f87,plain,(
% 3.50/0.99    ~r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),k1_setfam_1(k2_tarski(sK1,sK2)))),
% 3.50/0.99    inference(definition_unfolding,[],[f75,f60,f48])).
% 3.50/0.99  
% 3.50/0.99  cnf(c_23,negated_conjecture,
% 3.50/0.99      ( m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) ),
% 3.50/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1329,plain,
% 3.50/0.99      ( m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_24,negated_conjecture,
% 3.50/0.99      ( m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) ),
% 3.50/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1328,plain,
% 3.50/0.99      ( m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_9,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.50/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.50/0.99      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 3.50/0.99      | ~ v4_orders_2(X1)
% 3.50/0.99      | ~ v5_orders_2(X1)
% 3.50/0.99      | ~ v2_lattice3(X1)
% 3.50/0.99      | ~ l1_orders_2(X1)
% 3.50/0.99      | k11_lattice3(X1,k11_lattice3(X1,X2,X0),X3) = k11_lattice3(X1,X2,k11_lattice3(X1,X0,X3)) ),
% 3.50/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_25,negated_conjecture,
% 3.50/0.99      ( v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
% 3.50/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_560,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.50/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.50/0.99      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 3.50/0.99      | ~ v4_orders_2(X1)
% 3.50/0.99      | ~ v5_orders_2(X1)
% 3.50/0.99      | ~ l1_orders_2(X1)
% 3.50/0.99      | k11_lattice3(X1,X2,k11_lattice3(X1,X0,X3)) = k11_lattice3(X1,k11_lattice3(X1,X2,X0),X3)
% 3.50/0.99      | g1_orders_2(sK0,k1_yellow_1(sK0)) != X1 ),
% 3.50/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_25]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_561,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ v4_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
% 3.50/0.99      | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
% 3.50/0.99      | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
% 3.50/0.99      | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X2)) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1),X2) ),
% 3.50/0.99      inference(unflattening,[status(thm)],[c_560]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_15,plain,
% 3.50/0.99      ( v4_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
% 3.50/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_51,plain,
% 3.50/0.99      ( v4_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_14,plain,
% 3.50/0.99      ( v5_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
% 3.50/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_54,plain,
% 3.50/0.99      ( v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_12,plain,
% 3.50/0.99      ( l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
% 3.50/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_58,plain,
% 3.50/0.99      ( l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_565,plain,
% 3.50/0.99      ( ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X2)) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1),X2) ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_561,c_51,c_54,c_58]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_566,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,X0),X1) ),
% 3.50/0.99      inference(renaming,[status(thm)],[c_565]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1327,plain,
% 3.50/0.99      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X2)) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1),X2)
% 3.50/0.99      | m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
% 3.50/0.99      | m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
% 3.50/0.99      | m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_566]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2937,plain,
% 3.50/0.99      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,X0),X1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1))
% 3.50/0.99      | m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
% 3.50/0.99      | m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1328,c_1327]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3585,plain,
% 3.50/0.99      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),X0) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,X0))
% 3.50/0.99      | m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1329,c_2937]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3618,plain,
% 3.50/0.99      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2)) ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1329,c_3585]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_6,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.50/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.50/0.99      | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
% 3.50/0.99      | ~ l1_orders_2(X1) ),
% 3.50/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1333,plain,
% 3.50/0.99      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 3.50/0.99      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 3.50/0.99      | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1)) = iProver_top
% 3.50/0.99      | l1_orders_2(X1) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3762,plain,
% 3.50/0.99      ( m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2)),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) = iProver_top
% 3.50/0.99      | m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
% 3.50/0.99      | m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
% 3.50/0.99      | l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_3618,c_1333]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_29,plain,
% 3.50/0.99      ( m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_30,plain,
% 3.50/0.99      ( m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_57,plain,
% 3.50/0.99      ( l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_59,plain,
% 3.50/0.99      ( l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) = iProver_top ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_57]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1592,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))
% 3.50/0.99      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))
% 3.50/0.99      | m1_subset_1(k11_lattice3(g1_orders_2(X1,k1_yellow_1(X1)),X2,X0),u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))
% 3.50/0.99      | ~ l1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1904,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_1592]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2120,plain,
% 3.50/0.99      ( m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_1904]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2121,plain,
% 3.50/0.99      ( m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) = iProver_top
% 3.50/0.99      | m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
% 3.50/0.99      | l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_2120]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1955,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,sK2)),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_1592]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2293,plain,
% 3.50/0.99      ( ~ m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,sK2)),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_1955]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3556,plain,
% 3.50/0.99      ( ~ m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2)),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_2293]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3557,plain,
% 3.50/0.99      ( m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
% 3.50/0.99      | m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2)),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) = iProver_top
% 3.50/0.99      | m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
% 3.50/0.99      | l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_3556]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_7362,plain,
% 3.50/0.99      ( m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2)),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) = iProver_top ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_3762,c_29,c_30,c_59,c_2121,c_3557]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_10,plain,
% 3.50/0.99      ( ~ r3_orders_2(X0,X1,X2)
% 3.50/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.50/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.50/0.99      | ~ v5_orders_2(X0)
% 3.50/0.99      | ~ v2_lattice3(X0)
% 3.50/0.99      | ~ v3_orders_2(X0)
% 3.50/0.99      | ~ l1_orders_2(X0)
% 3.50/0.99      | k12_lattice3(X0,X1,X2) = X1 ),
% 3.50/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_536,plain,
% 3.50/0.99      ( ~ r3_orders_2(X0,X1,X2)
% 3.50/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.50/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.50/0.99      | ~ v5_orders_2(X0)
% 3.50/0.99      | ~ v3_orders_2(X0)
% 3.50/0.99      | ~ l1_orders_2(X0)
% 3.50/0.99      | k12_lattice3(X0,X1,X2) = X1
% 3.50/0.99      | g1_orders_2(sK0,k1_yellow_1(sK0)) != X0 ),
% 3.50/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_25]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_537,plain,
% 3.50/0.99      ( ~ r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)
% 3.50/0.99      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
% 3.50/0.99      | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
% 3.50/0.99      | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
% 3.50/0.99      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) = X0 ),
% 3.50/0.99      inference(unflattening,[status(thm)],[c_536]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_16,plain,
% 3.50/0.99      ( v3_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
% 3.50/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_48,plain,
% 3.50/0.99      ( v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_541,plain,
% 3.50/0.99      ( ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)
% 3.50/0.99      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) = X0 ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_537,c_48,c_54,c_58]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_542,plain,
% 3.50/0.99      ( ~ r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)
% 3.50/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) = X0 ),
% 3.50/0.99      inference(renaming,[status(thm)],[c_541]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_5,plain,
% 3.50/0.99      ( r3_orders_2(X0,X1,X1)
% 3.50/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.50/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.50/0.99      | v2_struct_0(X0)
% 3.50/0.99      | ~ v3_orders_2(X0)
% 3.50/0.99      | ~ l1_orders_2(X0) ),
% 3.50/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_19,plain,
% 3.50/0.99      ( v1_xboole_0(X0)
% 3.50/0.99      | ~ v2_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) ),
% 3.50/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_26,negated_conjecture,
% 3.50/0.99      ( ~ v1_xboole_0(sK0) ),
% 3.50/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_412,plain,
% 3.50/0.99      ( ~ v2_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) | sK0 != X0 ),
% 3.50/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_26]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_413,plain,
% 3.50/0.99      ( ~ v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
% 3.50/0.99      inference(unflattening,[status(thm)],[c_412]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_431,plain,
% 3.50/0.99      ( r3_orders_2(X0,X1,X1)
% 3.50/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.50/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.50/0.99      | ~ v3_orders_2(X0)
% 3.50/0.99      | ~ l1_orders_2(X0)
% 3.50/0.99      | g1_orders_2(sK0,k1_yellow_1(sK0)) != X0 ),
% 3.50/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_413]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_432,plain,
% 3.50/0.99      ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X0)
% 3.50/0.99      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
% 3.50/0.99      | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
% 3.50/0.99      inference(unflattening,[status(thm)],[c_431]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_436,plain,
% 3.50/0.99      ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X0)
% 3.50/0.99      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_432,c_48,c_58]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_437,plain,
% 3.50/0.99      ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X0)
% 3.50/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) ),
% 3.50/0.99      inference(renaming,[status(thm)],[c_436]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_722,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | X1 != X0
% 3.50/0.99      | X1 != X2
% 3.50/0.99      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,X0) = X2
% 3.50/0.99      | g1_orders_2(sK0,k1_yellow_1(sK0)) != g1_orders_2(sK0,k1_yellow_1(sK0)) ),
% 3.50/0.99      inference(resolution_lifted,[status(thm)],[c_542,c_437]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_723,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X0) = X0 ),
% 3.50/0.99      inference(unflattening,[status(thm)],[c_722]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_940,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X0) = X0
% 3.50/0.99      | ~ sP2_iProver_split ),
% 3.50/0.99      inference(splitting,
% 3.50/0.99                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 3.50/0.99                [c_723]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1321,plain,
% 3.50/0.99      ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X0) = X0
% 3.50/0.99      | m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
% 3.50/0.99      | sP2_iProver_split != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_940]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_941,plain,
% 3.50/0.99      ( sP2_iProver_split | sP0_iProver_split ),
% 3.50/0.99      inference(splitting,
% 3.50/0.99                [splitting(split),new_symbols(definition,[])],
% 3.50/0.99                [c_723]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_978,plain,
% 3.50/0.99      ( sP2_iProver_split = iProver_top
% 3.50/0.99      | sP0_iProver_split = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_941]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_979,plain,
% 3.50/0.99      ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X0) = X0
% 3.50/0.99      | m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
% 3.50/0.99      | sP2_iProver_split != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_940]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_21,plain,
% 3.50/0.99      ( ~ r3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2)
% 3.50/0.99      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
% 3.50/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
% 3.50/0.99      | r1_tarski(X1,X2)
% 3.50/0.99      | v1_xboole_0(X0) ),
% 3.50/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_376,plain,
% 3.50/0.99      ( ~ r3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2)
% 3.50/0.99      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
% 3.50/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
% 3.50/0.99      | r1_tarski(X1,X2)
% 3.50/0.99      | sK0 != X0 ),
% 3.50/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_26]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_377,plain,
% 3.50/0.99      ( ~ r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)
% 3.50/0.99      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | r1_tarski(X0,X1) ),
% 3.50/0.99      inference(unflattening,[status(thm)],[c_376]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_737,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | r1_tarski(X2,X0)
% 3.50/0.99      | X1 != X0
% 3.50/0.99      | X1 != X2
% 3.50/0.99      | g1_orders_2(sK0,k1_yellow_1(sK0)) != g1_orders_2(sK0,k1_yellow_1(sK0)) ),
% 3.50/0.99      inference(resolution_lifted,[status(thm)],[c_377,c_437]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_738,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | r1_tarski(X0,X0) ),
% 3.50/0.99      inference(unflattening,[status(thm)],[c_737]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_937,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ sP0_iProver_split ),
% 3.50/0.99      inference(splitting,
% 3.50/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.50/0.99                [c_738]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1319,plain,
% 3.50/0.99      ( m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
% 3.50/0.99      | sP0_iProver_split != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_937]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2285,plain,
% 3.50/0.99      ( sP0_iProver_split != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1329,c_1319]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3697,plain,
% 3.50/0.99      ( m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
% 3.50/0.99      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X0) = X0 ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_1321,c_978,c_979,c_2285]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3698,plain,
% 3.50/0.99      ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X0) = X0
% 3.50/0.99      | m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
% 3.50/0.99      inference(renaming,[status(thm)],[c_3697]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3704,plain,
% 3.50/0.99      ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2) = sK2 ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1329,c_3698]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_7,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.50/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.50/0.99      | ~ v5_orders_2(X1)
% 3.50/0.99      | ~ v2_lattice3(X1)
% 3.50/0.99      | ~ l1_orders_2(X1)
% 3.50/0.99      | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0) ),
% 3.50/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_605,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.50/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.50/0.99      | ~ v5_orders_2(X1)
% 3.50/0.99      | ~ l1_orders_2(X1)
% 3.50/0.99      | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0)
% 3.50/0.99      | g1_orders_2(sK0,k1_yellow_1(sK0)) != X1 ),
% 3.50/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_25]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_606,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
% 3.50/0.99      | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
% 3.50/0.99      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) ),
% 3.50/0.99      inference(unflattening,[status(thm)],[c_605]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_610,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_606,c_54,c_58]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_611,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0) ),
% 3.50/0.99      inference(renaming,[status(thm)],[c_610]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1325,plain,
% 3.50/0.99      ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)
% 3.50/0.99      | m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
% 3.50/0.99      | m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_611]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1566,plain,
% 3.50/0.99      ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,X0) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,X0)
% 3.50/0.99      | m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1329,c_1325]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1610,plain,
% 3.50/0.99      ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2) ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1329,c_1566]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3722,plain,
% 3.50/0.99      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2) = sK2 ),
% 3.50/0.99      inference(demodulation,[status(thm)],[c_3704,c_1610]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_7366,plain,
% 3.50/0.99      ( m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) = iProver_top ),
% 3.50/0.99      inference(light_normalisation,[status(thm)],[c_7362,c_3722]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_7402,plain,
% 3.50/0.99      ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),X0) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),X0)
% 3.50/0.99      | m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_7366,c_1325]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_7578,plain,
% 3.50/0.99      ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1329,c_7402]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_4365,plain,
% 3.50/0.99      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) ),
% 3.50/0.99      inference(demodulation,[status(thm)],[c_3722,c_3618]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_7587,plain,
% 3.50/0.99      ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) ),
% 3.50/0.99      inference(light_normalisation,[status(thm)],[c_7578,c_4365]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_7579,plain,
% 3.50/0.99      ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1328,c_7402]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3619,plain,
% 3.50/0.99      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1)) ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1328,c_3585]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_8,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.50/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.50/0.99      | ~ v5_orders_2(X1)
% 3.50/0.99      | ~ v2_lattice3(X1)
% 3.50/0.99      | ~ l1_orders_2(X1)
% 3.50/0.99      | k11_lattice3(X1,X0,X2) = k11_lattice3(X1,X2,X0) ),
% 3.50/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_584,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.50/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.50/0.99      | ~ v5_orders_2(X1)
% 3.50/0.99      | ~ l1_orders_2(X1)
% 3.50/0.99      | k11_lattice3(X1,X0,X2) = k11_lattice3(X1,X2,X0)
% 3.50/0.99      | g1_orders_2(sK0,k1_yellow_1(sK0)) != X1 ),
% 3.50/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_25]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_585,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
% 3.50/0.99      | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
% 3.50/0.99      | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) ),
% 3.50/0.99      inference(unflattening,[status(thm)],[c_584]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_589,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_585,c_54,c_58]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_590,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0) ),
% 3.50/0.99      inference(renaming,[status(thm)],[c_589]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1326,plain,
% 3.50/0.99      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0)
% 3.50/0.99      | m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top
% 3.50/0.99      | m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_590]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2211,plain,
% 3.50/0.99      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,X0)
% 3.50/0.99      | m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1329,c_1326]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2272,plain,
% 3.50/0.99      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1328,c_2211]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3621,plain,
% 3.50/0.99      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2)) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) ),
% 3.50/0.99      inference(light_normalisation,[status(thm)],[c_3619,c_2272]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3705,plain,
% 3.50/0.99      ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1) = sK1 ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1328,c_3698]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1567,plain,
% 3.50/0.99      ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,X0) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,X0)
% 3.50/0.99      | m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1328,c_1325]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1642,plain,
% 3.50/0.99      ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1) ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1328,c_1567]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3760,plain,
% 3.50/0.99      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1) = sK1 ),
% 3.50/0.99      inference(demodulation,[status(thm)],[c_3705,c_1642]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3586,plain,
% 3.50/0.99      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1),X0) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,X0))
% 3.50/0.99      | m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1328,c_2937]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3951,plain,
% 3.50/0.99      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1),sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2)) ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1329,c_3586]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_5122,plain,
% 3.50/0.99      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2)) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) ),
% 3.50/0.99      inference(demodulation,[status(thm)],[c_3760,c_3951]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_6641,plain,
% 3.50/0.99      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) ),
% 3.50/0.99      inference(light_normalisation,[status(thm)],[c_3621,c_5122]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_7584,plain,
% 3.50/0.99      ( k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) ),
% 3.50/0.99      inference(light_normalisation,[status(thm)],[c_7579,c_6641]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_11,plain,
% 3.50/0.99      ( r3_orders_2(X0,X1,X2)
% 3.50/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.50/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.50/0.99      | ~ v5_orders_2(X0)
% 3.50/0.99      | ~ v2_lattice3(X0)
% 3.50/0.99      | ~ v3_orders_2(X0)
% 3.50/0.99      | ~ l1_orders_2(X0)
% 3.50/0.99      | k12_lattice3(X0,X1,X2) != X1 ),
% 3.50/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_516,plain,
% 3.50/0.99      ( r3_orders_2(X0,X1,X2)
% 3.50/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.50/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.50/0.99      | ~ v5_orders_2(X0)
% 3.50/0.99      | ~ v3_orders_2(X0)
% 3.50/0.99      | ~ l1_orders_2(X0)
% 3.50/0.99      | k12_lattice3(X0,X1,X2) != X1
% 3.50/0.99      | g1_orders_2(sK0,k1_yellow_1(sK0)) != X0 ),
% 3.50/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_25]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_517,plain,
% 3.50/0.99      ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)
% 3.50/0.99      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
% 3.50/0.99      | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
% 3.50/0.99      | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
% 3.50/0.99      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) != X0 ),
% 3.50/0.99      inference(unflattening,[status(thm)],[c_516]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_519,plain,
% 3.50/0.99      ( ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)
% 3.50/0.99      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) != X0 ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_517,c_48,c_54,c_58]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_520,plain,
% 3.50/0.99      ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)
% 3.50/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) != X0 ),
% 3.50/0.99      inference(renaming,[status(thm)],[c_519]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_687,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | r1_tarski(X0,X1)
% 3.50/0.99      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) != X0 ),
% 3.50/0.99      inference(resolution,[status(thm)],[c_520,c_377]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1965,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,sK2),X0)
% 3.50/0.99      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,sK2),X0) != k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,sK2) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_687]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2429,plain,
% 3.50/0.99      ( ~ m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,sK2),sK1)
% 3.50/0.99      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,sK2),sK1) != k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,sK2) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_1965]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3782,plain,
% 3.50/0.99      ( ~ m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1)
% 3.50/0.99      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) != k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_2429]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2424,plain,
% 3.50/0.99      ( ~ m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,sK2),sK2)
% 3.50/0.99      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,sK2),sK2) != k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,sK2) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_1965]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3756,plain,
% 3.50/0.99      ( ~ m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2)
% 3.50/0.99      | k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) != k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_2424]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_0,plain,
% 3.50/0.99      ( ~ r1_tarski(X0,X1)
% 3.50/0.99      | ~ r1_tarski(X0,X2)
% 3.50/0.99      | r1_tarski(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
% 3.50/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1338,plain,
% 3.50/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.50/0.99      | r1_tarski(X0,X2) != iProver_top
% 3.50/0.99      | r1_tarski(X0,k1_setfam_1(k2_tarski(X2,X1))) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_22,negated_conjecture,
% 3.50/0.99      ( ~ r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),k1_setfam_1(k2_tarski(sK1,sK2))) ),
% 3.50/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1330,plain,
% 3.50/0.99      ( r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),k1_setfam_1(k2_tarski(sK1,sK2))) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2458,plain,
% 3.50/0.99      ( r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) != iProver_top
% 3.50/0.99      | r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1338,c_1330]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2459,plain,
% 3.50/0.99      ( ~ r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2)
% 3.50/0.99      | ~ r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) ),
% 3.50/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2458]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2123,plain,
% 3.50/0.99      ( m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
% 3.50/0.99      | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_1904]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(contradiction,plain,
% 3.50/0.99      ( $false ),
% 3.50/0.99      inference(minisat,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_7587,c_7584,c_3782,c_3756,c_2459,c_2123,c_58,c_23,
% 3.50/0.99                 c_24]) ).
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.50/0.99  
% 3.50/0.99  ------                               Statistics
% 3.50/0.99  
% 3.50/0.99  ------ General
% 3.50/0.99  
% 3.50/0.99  abstr_ref_over_cycles:                  0
% 3.50/0.99  abstr_ref_under_cycles:                 0
% 3.50/0.99  gc_basic_clause_elim:                   0
% 3.50/0.99  forced_gc_time:                         0
% 3.50/0.99  parsing_time:                           0.01
% 3.50/0.99  unif_index_cands_time:                  0.
% 3.50/0.99  unif_index_add_time:                    0.
% 3.50/0.99  orderings_time:                         0.
% 3.50/0.99  out_proof_time:                         0.012
% 3.50/0.99  total_time:                             0.267
% 3.50/0.99  num_of_symbols:                         58
% 3.50/0.99  num_of_terms:                           9161
% 3.50/0.99  
% 3.50/0.99  ------ Preprocessing
% 3.50/0.99  
% 3.50/0.99  num_of_splits:                          4
% 3.50/0.99  num_of_split_atoms:                     3
% 3.50/0.99  num_of_reused_defs:                     1
% 3.50/0.99  num_eq_ax_congr_red:                    12
% 3.50/0.99  num_of_sem_filtered_clauses:            4
% 3.50/0.99  num_of_subtypes:                        0
% 3.50/0.99  monotx_restored_types:                  0
% 3.50/0.99  sat_num_of_epr_types:                   0
% 3.50/0.99  sat_num_of_non_cyclic_types:            0
% 3.50/0.99  sat_guarded_non_collapsed_types:        0
% 3.50/0.99  num_pure_diseq_elim:                    0
% 3.50/0.99  simp_replaced_by:                       0
% 3.50/0.99  res_preprocessed:                       113
% 3.50/0.99  prep_upred:                             0
% 3.50/0.99  prep_unflattend:                        25
% 3.50/0.99  smt_new_axioms:                         0
% 3.50/0.99  pred_elim_cands:                        4
% 3.50/0.99  pred_elim:                              7
% 3.50/0.99  pred_elim_cl:                           7
% 3.50/0.99  pred_elim_cycles:                       15
% 3.50/0.99  merged_defs:                            0
% 3.50/0.99  merged_defs_ncl:                        0
% 3.50/0.99  bin_hyper_res:                          0
% 3.50/0.99  prep_cycles:                            4
% 3.50/0.99  pred_elim_time:                         0.012
% 3.50/0.99  splitting_time:                         0.
% 3.50/0.99  sem_filter_time:                        0.
% 3.50/0.99  monotx_time:                            0.
% 3.50/0.99  subtype_inf_time:                       0.
% 3.50/0.99  
% 3.50/0.99  ------ Problem properties
% 3.50/0.99  
% 3.50/0.99  clauses:                                22
% 3.50/0.99  conjectures:                            3
% 3.50/0.99  epr:                                    2
% 3.50/0.99  horn:                                   20
% 3.50/0.99  ground:                                 5
% 3.50/0.99  unary:                                  5
% 3.50/0.99  binary:                                 5
% 3.50/0.99  lits:                                   55
% 3.50/0.99  lits_eq:                                11
% 3.50/0.99  fd_pure:                                0
% 3.50/0.99  fd_pseudo:                              0
% 3.50/0.99  fd_cond:                                0
% 3.50/0.99  fd_pseudo_cond:                         2
% 3.50/0.99  ac_symbols:                             0
% 3.50/0.99  
% 3.50/0.99  ------ Propositional Solver
% 3.50/0.99  
% 3.50/0.99  prop_solver_calls:                      28
% 3.50/0.99  prop_fast_solver_calls:                 980
% 3.50/0.99  smt_solver_calls:                       0
% 3.50/0.99  smt_fast_solver_calls:                  0
% 3.50/0.99  prop_num_of_clauses:                    3565
% 3.50/0.99  prop_preprocess_simplified:             7578
% 3.50/0.99  prop_fo_subsumed:                       44
% 3.50/0.99  prop_solver_time:                       0.
% 3.50/0.99  smt_solver_time:                        0.
% 3.50/0.99  smt_fast_solver_time:                   0.
% 3.50/0.99  prop_fast_solver_time:                  0.
% 3.50/0.99  prop_unsat_core_time:                   0.
% 3.50/0.99  
% 3.50/0.99  ------ QBF
% 3.50/0.99  
% 3.50/0.99  qbf_q_res:                              0
% 3.50/0.99  qbf_num_tautologies:                    0
% 3.50/0.99  qbf_prep_cycles:                        0
% 3.50/0.99  
% 3.50/0.99  ------ BMC1
% 3.50/0.99  
% 3.50/0.99  bmc1_current_bound:                     -1
% 3.50/0.99  bmc1_last_solved_bound:                 -1
% 3.50/0.99  bmc1_unsat_core_size:                   -1
% 3.50/0.99  bmc1_unsat_core_parents_size:           -1
% 3.50/0.99  bmc1_merge_next_fun:                    0
% 3.50/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.50/0.99  
% 3.50/0.99  ------ Instantiation
% 3.50/0.99  
% 3.50/0.99  inst_num_of_clauses:                    1006
% 3.50/0.99  inst_num_in_passive:                    313
% 3.50/0.99  inst_num_in_active:                     321
% 3.50/0.99  inst_num_in_unprocessed:                372
% 3.50/0.99  inst_num_of_loops:                      410
% 3.50/0.99  inst_num_of_learning_restarts:          0
% 3.50/0.99  inst_num_moves_active_passive:          86
% 3.50/0.99  inst_lit_activity:                      0
% 3.50/0.99  inst_lit_activity_moves:                1
% 3.50/0.99  inst_num_tautologies:                   0
% 3.50/0.99  inst_num_prop_implied:                  0
% 3.50/0.99  inst_num_existing_simplified:           0
% 3.50/0.99  inst_num_eq_res_simplified:             0
% 3.50/0.99  inst_num_child_elim:                    0
% 3.50/0.99  inst_num_of_dismatching_blockings:      309
% 3.50/0.99  inst_num_of_non_proper_insts:           541
% 3.50/0.99  inst_num_of_duplicates:                 0
% 3.50/0.99  inst_inst_num_from_inst_to_res:         0
% 3.50/0.99  inst_dismatching_checking_time:         0.
% 3.50/0.99  
% 3.50/0.99  ------ Resolution
% 3.50/0.99  
% 3.50/0.99  res_num_of_clauses:                     0
% 3.50/0.99  res_num_in_passive:                     0
% 3.50/0.99  res_num_in_active:                      0
% 3.50/0.99  res_num_of_loops:                       117
% 3.50/0.99  res_forward_subset_subsumed:            14
% 3.50/0.99  res_backward_subset_subsumed:           0
% 3.50/0.99  res_forward_subsumed:                   0
% 3.50/0.99  res_backward_subsumed:                  0
% 3.50/0.99  res_forward_subsumption_resolution:     2
% 3.50/0.99  res_backward_subsumption_resolution:    0
% 3.50/0.99  res_clause_to_clause_subsumption:       626
% 3.50/0.99  res_orphan_elimination:                 0
% 3.50/0.99  res_tautology_del:                      20
% 3.50/0.99  res_num_eq_res_simplified:              0
% 3.50/0.99  res_num_sel_changes:                    0
% 3.50/0.99  res_moves_from_active_to_pass:          0
% 3.50/0.99  
% 3.50/0.99  ------ Superposition
% 3.50/0.99  
% 3.50/0.99  sup_time_total:                         0.
% 3.50/0.99  sup_time_generating:                    0.
% 3.50/0.99  sup_time_sim_full:                      0.
% 3.50/0.99  sup_time_sim_immed:                     0.
% 3.50/0.99  
% 3.50/0.99  sup_num_of_clauses:                     133
% 3.50/0.99  sup_num_in_active:                      71
% 3.50/0.99  sup_num_in_passive:                     62
% 3.50/0.99  sup_num_of_loops:                       81
% 3.50/0.99  sup_fw_superposition:                   130
% 3.50/0.99  sup_bw_superposition:                   59
% 3.50/0.99  sup_immediate_simplified:               54
% 3.50/0.99  sup_given_eliminated:                   2
% 3.50/0.99  comparisons_done:                       0
% 3.50/0.99  comparisons_avoided:                    0
% 3.50/0.99  
% 3.50/0.99  ------ Simplifications
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  sim_fw_subset_subsumed:                 7
% 3.50/0.99  sim_bw_subset_subsumed:                 2
% 3.50/0.99  sim_fw_subsumed:                        6
% 3.50/0.99  sim_bw_subsumed:                        0
% 3.50/0.99  sim_fw_subsumption_res:                 0
% 3.50/0.99  sim_bw_subsumption_res:                 0
% 3.50/0.99  sim_tautology_del:                      0
% 3.50/0.99  sim_eq_tautology_del:                   31
% 3.50/0.99  sim_eq_res_simp:                        0
% 3.50/0.99  sim_fw_demodulated:                     4
% 3.50/0.99  sim_bw_demodulated:                     11
% 3.50/0.99  sim_light_normalised:                   40
% 3.50/0.99  sim_joinable_taut:                      0
% 3.50/0.99  sim_joinable_simp:                      0
% 3.50/0.99  sim_ac_normalised:                      0
% 3.50/0.99  sim_smt_subsumption:                    0
% 3.50/0.99  
%------------------------------------------------------------------------------
