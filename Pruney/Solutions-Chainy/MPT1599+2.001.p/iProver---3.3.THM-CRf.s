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
% DateTime   : Thu Dec  3 12:20:07 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 343 expanded)
%              Number of clauses        :   65 (  98 expanded)
%              Number of leaves         :   14 (  87 expanded)
%              Depth                    :   20
%              Number of atoms          :  587 (1411 expanded)
%              Number of equality atoms :   50 ( 112 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   21 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f13,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v2_lattice3(k2_yellow_1(X0))
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
               => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
          & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
     => ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,sK3),k3_xboole_0(X1,sK3))
        & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f43,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k3_xboole_0(sK2,sK3))
    & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
    & v2_lattice3(k2_yellow_1(sK1))
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f32,f42,f41,f40])).

fof(f72,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k3_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0] : g1_orders_2(X0,k1_yellow_1(X0)) = k2_yellow_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : g1_orders_2(X0,k1_yellow_1(X0)) = k2_yellow_1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f80,plain,(
    ~ r1_tarski(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),k3_xboole_0(sK2,sK3)) ),
    inference(definition_unfolding,[],[f72,f60])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f66,f60,f60,f60])).

fof(f68,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f69,plain,(
    v2_lattice3(k2_yellow_1(sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f83,plain,(
    v2_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1))) ),
    inference(definition_unfolding,[],[f69,f60])).

fof(f11,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f64,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f76,plain,(
    ! [X0] : v3_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f64,f60])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f73,plain,(
    ! [X0] : l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f62,f60])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

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
    inference(nnf_transformation,[],[f29])).

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
     => ( ~ r1_orders_2(X0,sK0(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK0(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK0(X0,X1,X2,X3),X1)
        & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
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
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).

fof(f53,plain,(
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
    inference(cnf_transformation,[],[f38])).

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
    inference(equality_resolution,[],[f53])).

fof(f65,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f75,plain,(
    ! [X0] : v5_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f65,f60])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X2)
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f71,plain,(
    m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f81,plain,(
    m1_subset_1(sK3,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) ),
    inference(definition_unfolding,[],[f71,f60])).

fof(f70,plain,(
    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f82,plain,(
    m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) ),
    inference(definition_unfolding,[],[f70,f60])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1537,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k3_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_23,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),k3_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1529,plain,
    ( r1_tarski(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),k3_xboole_0(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2696,plain,
    ( r1_tarski(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),sK3) != iProver_top
    | r1_tarski(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1537,c_1529])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1850,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))
    | m1_subset_1(k11_lattice3(g1_orders_2(X1,k1_yellow_1(X1)),X2,X0),u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))
    | ~ l1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2241,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | m1_subset_1(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,sK3),u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | ~ m1_subset_1(sK3,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | ~ l1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1))) ),
    inference(instantiation,[status(thm)],[c_1850])).

cnf(c_2597,plain,
    ( m1_subset_1(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | ~ m1_subset_1(sK3,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | ~ m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | ~ l1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1))) ),
    inference(instantiation,[status(thm)],[c_2241])).

cnf(c_2598,plain,
    ( m1_subset_1(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) != iProver_top
    | l1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2597])).

cnf(c_5,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_7,plain,
    ( ~ v2_lattice3(X0)
    | ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_493,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_5,c_7])).

cnf(c_22,plain,
    ( ~ r3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
    | r1_tarski(X1,X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_27,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_357,plain,
    ( ~ r3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
    | r1_tarski(X1,X2)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_27])).

cnf(c_358,plain,
    ( ~ r3_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | r1_tarski(X0,X1) ),
    inference(unflattening,[status(thm)],[c_357])).

cnf(c_601,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | ~ m1_subset_1(X4,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | r1_tarski(X3,X4)
    | ~ v2_lattice3(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | X3 != X1
    | X4 != X2
    | g1_orders_2(sK1,k1_yellow_1(sK1)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_493,c_358])).

cnf(c_602,plain,
    ( ~ r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | r1_tarski(X0,X1)
    | ~ v2_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)))
    | ~ v3_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)))
    | ~ l1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1))) ),
    inference(unflattening,[status(thm)],[c_601])).

cnf(c_26,negated_conjecture,
    ( v2_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_19,plain,
    ( v3_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_43,plain,
    ( v3_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1))) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_16,plain,
    ( l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_50,plain,
    ( l1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1))) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_606,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | ~ r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_602,c_26,c_43,c_50])).

cnf(c_607,plain,
    ( ~ r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_606])).

cnf(c_1790,plain,
    ( ~ r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | ~ m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | r1_tarski(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_607])).

cnf(c_2314,plain,
    ( ~ r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),sK2)
    | ~ m1_subset_1(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | ~ m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | r1_tarski(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_1790])).

cnf(c_2320,plain,
    ( r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),sK2) != iProver_top
    | m1_subset_1(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) != iProver_top
    | r1_tarski(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2314])).

cnf(c_1785,plain,
    ( ~ r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | ~ m1_subset_1(sK3,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | r1_tarski(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_607])).

cnf(c_2285,plain,
    ( ~ r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),sK3)
    | ~ m1_subset_1(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | ~ m1_subset_1(sK3,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | r1_tarski(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_1785])).

cnf(c_2291,plain,
    ( r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),sK3) != iProver_top
    | m1_subset_1(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) != iProver_top
    | r1_tarski(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2285])).

cnf(c_931,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
    | g1_orders_2(X3,k1_yellow_1(X3)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_16])).

cnf(c_932,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))
    | m1_subset_1(k11_lattice3(g1_orders_2(X1,k1_yellow_1(X1)),X0,X2),u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1)))) ),
    inference(unflattening,[status(thm)],[c_931])).

cnf(c_15,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_163,plain,
    ( ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_7])).

cnf(c_164,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_163])).

cnf(c_844,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | g1_orders_2(sK1,k1_yellow_1(sK1)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_164,c_26])).

cnf(c_845,plain,
    ( r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | ~ m1_subset_1(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,X1),u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | ~ v5_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)))
    | ~ l1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1))) ),
    inference(unflattening,[status(thm)],[c_844])).

cnf(c_18,plain,
    ( v5_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_46,plain,
    ( v5_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1))) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_847,plain,
    ( r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | ~ m1_subset_1(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,X1),u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_845,c_46,c_50])).

cnf(c_848,plain,
    ( r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | ~ m1_subset_1(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,X1),u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) ),
    inference(renaming,[status(thm)],[c_847])).

cnf(c_952,plain,
    ( r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_932,c_848])).

cnf(c_1765,plain,
    ( r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | ~ m1_subset_1(sK3,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) ),
    inference(instantiation,[status(thm)],[c_952])).

cnf(c_2000,plain,
    ( r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | ~ m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) ),
    inference(instantiation,[status(thm)],[c_1765])).

cnf(c_2001,plain,
    ( r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2000])).

cnf(c_14,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_170,plain,
    ( ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_7])).

cnf(c_171,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_170])).

cnf(c_820,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | g1_orders_2(sK1,k1_yellow_1(sK1)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_171,c_26])).

cnf(c_821,plain,
    ( r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | ~ m1_subset_1(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,X1),u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | ~ v5_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)))
    | ~ l1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1))) ),
    inference(unflattening,[status(thm)],[c_820])).

cnf(c_825,plain,
    ( r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | ~ m1_subset_1(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,X1),u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_821,c_46,c_50])).

cnf(c_826,plain,
    ( r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | ~ m1_subset_1(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,X1),u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) ),
    inference(renaming,[status(thm)],[c_825])).

cnf(c_953,plain,
    ( r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_932,c_826])).

cnf(c_1775,plain,
    ( r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,sK3),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | ~ m1_subset_1(sK3,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) ),
    inference(instantiation,[status(thm)],[c_953])).

cnf(c_1996,plain,
    ( r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
    | ~ m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) ),
    inference(instantiation,[status(thm)],[c_1775])).

cnf(c_1997,plain,
    ( r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),sK3) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1996])).

cnf(c_49,plain,
    ( l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_51,plain,
    ( l1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_49])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_31,plain,
    ( m1_subset_1(sK3,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_30,plain,
    ( m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2696,c_2598,c_2320,c_2291,c_2001,c_1997,c_51,c_31,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:39:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.22/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/0.99  
% 2.22/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.22/0.99  
% 2.22/0.99  ------  iProver source info
% 2.22/0.99  
% 2.22/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.22/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.22/0.99  git: non_committed_changes: false
% 2.22/0.99  git: last_make_outside_of_git: false
% 2.22/0.99  
% 2.22/0.99  ------ 
% 2.22/0.99  
% 2.22/0.99  ------ Input Options
% 2.22/0.99  
% 2.22/0.99  --out_options                           all
% 2.22/0.99  --tptp_safe_out                         true
% 2.22/0.99  --problem_path                          ""
% 2.22/0.99  --include_path                          ""
% 2.22/0.99  --clausifier                            res/vclausify_rel
% 2.22/0.99  --clausifier_options                    --mode clausify
% 2.22/0.99  --stdin                                 false
% 2.22/0.99  --stats_out                             all
% 2.22/0.99  
% 2.22/0.99  ------ General Options
% 2.22/0.99  
% 2.22/0.99  --fof                                   false
% 2.22/0.99  --time_out_real                         305.
% 2.22/0.99  --time_out_virtual                      -1.
% 2.22/0.99  --symbol_type_check                     false
% 2.22/0.99  --clausify_out                          false
% 2.22/0.99  --sig_cnt_out                           false
% 2.22/0.99  --trig_cnt_out                          false
% 2.22/0.99  --trig_cnt_out_tolerance                1.
% 2.22/0.99  --trig_cnt_out_sk_spl                   false
% 2.22/0.99  --abstr_cl_out                          false
% 2.22/0.99  
% 2.22/0.99  ------ Global Options
% 2.22/0.99  
% 2.22/0.99  --schedule                              default
% 2.22/0.99  --add_important_lit                     false
% 2.22/0.99  --prop_solver_per_cl                    1000
% 2.22/0.99  --min_unsat_core                        false
% 2.22/0.99  --soft_assumptions                      false
% 2.22/0.99  --soft_lemma_size                       3
% 2.22/0.99  --prop_impl_unit_size                   0
% 2.22/0.99  --prop_impl_unit                        []
% 2.22/0.99  --share_sel_clauses                     true
% 2.22/0.99  --reset_solvers                         false
% 2.22/0.99  --bc_imp_inh                            [conj_cone]
% 2.22/0.99  --conj_cone_tolerance                   3.
% 2.22/0.99  --extra_neg_conj                        none
% 2.22/0.99  --large_theory_mode                     true
% 2.22/0.99  --prolific_symb_bound                   200
% 2.22/0.99  --lt_threshold                          2000
% 2.22/0.99  --clause_weak_htbl                      true
% 2.22/0.99  --gc_record_bc_elim                     false
% 2.22/0.99  
% 2.22/0.99  ------ Preprocessing Options
% 2.22/0.99  
% 2.22/0.99  --preprocessing_flag                    true
% 2.22/0.99  --time_out_prep_mult                    0.1
% 2.22/0.99  --splitting_mode                        input
% 2.22/0.99  --splitting_grd                         true
% 2.22/0.99  --splitting_cvd                         false
% 2.22/0.99  --splitting_cvd_svl                     false
% 2.22/0.99  --splitting_nvd                         32
% 2.22/0.99  --sub_typing                            true
% 2.22/0.99  --prep_gs_sim                           true
% 2.22/0.99  --prep_unflatten                        true
% 2.22/0.99  --prep_res_sim                          true
% 2.22/0.99  --prep_upred                            true
% 2.22/0.99  --prep_sem_filter                       exhaustive
% 2.22/0.99  --prep_sem_filter_out                   false
% 2.22/0.99  --pred_elim                             true
% 2.22/0.99  --res_sim_input                         true
% 2.22/0.99  --eq_ax_congr_red                       true
% 2.22/0.99  --pure_diseq_elim                       true
% 2.22/0.99  --brand_transform                       false
% 2.22/0.99  --non_eq_to_eq                          false
% 2.22/0.99  --prep_def_merge                        true
% 2.22/0.99  --prep_def_merge_prop_impl              false
% 2.22/0.99  --prep_def_merge_mbd                    true
% 2.22/0.99  --prep_def_merge_tr_red                 false
% 2.22/0.99  --prep_def_merge_tr_cl                  false
% 2.22/0.99  --smt_preprocessing                     true
% 2.22/0.99  --smt_ac_axioms                         fast
% 2.22/0.99  --preprocessed_out                      false
% 2.22/0.99  --preprocessed_stats                    false
% 2.22/0.99  
% 2.22/0.99  ------ Abstraction refinement Options
% 2.22/0.99  
% 2.22/0.99  --abstr_ref                             []
% 2.22/0.99  --abstr_ref_prep                        false
% 2.22/0.99  --abstr_ref_until_sat                   false
% 2.22/0.99  --abstr_ref_sig_restrict                funpre
% 2.22/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.22/0.99  --abstr_ref_under                       []
% 2.22/0.99  
% 2.22/0.99  ------ SAT Options
% 2.22/0.99  
% 2.22/0.99  --sat_mode                              false
% 2.22/0.99  --sat_fm_restart_options                ""
% 2.22/0.99  --sat_gr_def                            false
% 2.22/0.99  --sat_epr_types                         true
% 2.22/0.99  --sat_non_cyclic_types                  false
% 2.22/0.99  --sat_finite_models                     false
% 2.22/0.99  --sat_fm_lemmas                         false
% 2.22/0.99  --sat_fm_prep                           false
% 2.22/0.99  --sat_fm_uc_incr                        true
% 2.22/0.99  --sat_out_model                         small
% 2.22/0.99  --sat_out_clauses                       false
% 2.22/0.99  
% 2.22/0.99  ------ QBF Options
% 2.22/0.99  
% 2.22/0.99  --qbf_mode                              false
% 2.22/0.99  --qbf_elim_univ                         false
% 2.22/0.99  --qbf_dom_inst                          none
% 2.22/0.99  --qbf_dom_pre_inst                      false
% 2.22/0.99  --qbf_sk_in                             false
% 2.22/0.99  --qbf_pred_elim                         true
% 2.22/0.99  --qbf_split                             512
% 2.22/0.99  
% 2.22/0.99  ------ BMC1 Options
% 2.22/0.99  
% 2.22/0.99  --bmc1_incremental                      false
% 2.22/0.99  --bmc1_axioms                           reachable_all
% 2.22/0.99  --bmc1_min_bound                        0
% 2.22/0.99  --bmc1_max_bound                        -1
% 2.22/0.99  --bmc1_max_bound_default                -1
% 2.22/0.99  --bmc1_symbol_reachability              true
% 2.22/0.99  --bmc1_property_lemmas                  false
% 2.22/0.99  --bmc1_k_induction                      false
% 2.22/0.99  --bmc1_non_equiv_states                 false
% 2.22/0.99  --bmc1_deadlock                         false
% 2.22/0.99  --bmc1_ucm                              false
% 2.22/0.99  --bmc1_add_unsat_core                   none
% 2.22/0.99  --bmc1_unsat_core_children              false
% 2.22/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.22/0.99  --bmc1_out_stat                         full
% 2.22/0.99  --bmc1_ground_init                      false
% 2.22/0.99  --bmc1_pre_inst_next_state              false
% 2.22/0.99  --bmc1_pre_inst_state                   false
% 2.22/0.99  --bmc1_pre_inst_reach_state             false
% 2.22/0.99  --bmc1_out_unsat_core                   false
% 2.22/0.99  --bmc1_aig_witness_out                  false
% 2.22/0.99  --bmc1_verbose                          false
% 2.22/0.99  --bmc1_dump_clauses_tptp                false
% 2.22/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.22/0.99  --bmc1_dump_file                        -
% 2.22/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.22/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.22/0.99  --bmc1_ucm_extend_mode                  1
% 2.22/0.99  --bmc1_ucm_init_mode                    2
% 2.22/0.99  --bmc1_ucm_cone_mode                    none
% 2.22/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.22/0.99  --bmc1_ucm_relax_model                  4
% 2.22/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.22/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.22/0.99  --bmc1_ucm_layered_model                none
% 2.22/0.99  --bmc1_ucm_max_lemma_size               10
% 2.22/0.99  
% 2.22/0.99  ------ AIG Options
% 2.22/0.99  
% 2.22/0.99  --aig_mode                              false
% 2.22/0.99  
% 2.22/0.99  ------ Instantiation Options
% 2.22/0.99  
% 2.22/0.99  --instantiation_flag                    true
% 2.22/0.99  --inst_sos_flag                         false
% 2.22/0.99  --inst_sos_phase                        true
% 2.22/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.22/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.22/0.99  --inst_lit_sel_side                     num_symb
% 2.22/0.99  --inst_solver_per_active                1400
% 2.22/0.99  --inst_solver_calls_frac                1.
% 2.22/0.99  --inst_passive_queue_type               priority_queues
% 2.22/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.22/0.99  --inst_passive_queues_freq              [25;2]
% 2.22/0.99  --inst_dismatching                      true
% 2.22/0.99  --inst_eager_unprocessed_to_passive     true
% 2.22/0.99  --inst_prop_sim_given                   true
% 2.22/0.99  --inst_prop_sim_new                     false
% 2.22/0.99  --inst_subs_new                         false
% 2.22/0.99  --inst_eq_res_simp                      false
% 2.22/0.99  --inst_subs_given                       false
% 2.22/0.99  --inst_orphan_elimination               true
% 2.22/0.99  --inst_learning_loop_flag               true
% 2.22/0.99  --inst_learning_start                   3000
% 2.22/0.99  --inst_learning_factor                  2
% 2.22/0.99  --inst_start_prop_sim_after_learn       3
% 2.22/0.99  --inst_sel_renew                        solver
% 2.22/0.99  --inst_lit_activity_flag                true
% 2.22/0.99  --inst_restr_to_given                   false
% 2.22/0.99  --inst_activity_threshold               500
% 2.22/0.99  --inst_out_proof                        true
% 2.22/0.99  
% 2.22/0.99  ------ Resolution Options
% 2.22/0.99  
% 2.22/0.99  --resolution_flag                       true
% 2.22/0.99  --res_lit_sel                           adaptive
% 2.22/0.99  --res_lit_sel_side                      none
% 2.22/0.99  --res_ordering                          kbo
% 2.22/0.99  --res_to_prop_solver                    active
% 2.22/0.99  --res_prop_simpl_new                    false
% 2.22/0.99  --res_prop_simpl_given                  true
% 2.22/0.99  --res_passive_queue_type                priority_queues
% 2.22/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.22/0.99  --res_passive_queues_freq               [15;5]
% 2.22/0.99  --res_forward_subs                      full
% 2.22/0.99  --res_backward_subs                     full
% 2.22/0.99  --res_forward_subs_resolution           true
% 2.22/0.99  --res_backward_subs_resolution          true
% 2.22/0.99  --res_orphan_elimination                true
% 2.22/0.99  --res_time_limit                        2.
% 2.22/0.99  --res_out_proof                         true
% 2.22/0.99  
% 2.22/0.99  ------ Superposition Options
% 2.22/0.99  
% 2.22/0.99  --superposition_flag                    true
% 2.22/0.99  --sup_passive_queue_type                priority_queues
% 2.22/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.22/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.22/0.99  --demod_completeness_check              fast
% 2.22/0.99  --demod_use_ground                      true
% 2.22/0.99  --sup_to_prop_solver                    passive
% 2.22/0.99  --sup_prop_simpl_new                    true
% 2.22/0.99  --sup_prop_simpl_given                  true
% 2.22/0.99  --sup_fun_splitting                     false
% 2.22/0.99  --sup_smt_interval                      50000
% 2.22/0.99  
% 2.22/0.99  ------ Superposition Simplification Setup
% 2.22/0.99  
% 2.22/0.99  --sup_indices_passive                   []
% 2.22/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.22/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/0.99  --sup_full_bw                           [BwDemod]
% 2.22/0.99  --sup_immed_triv                        [TrivRules]
% 2.22/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.22/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/0.99  --sup_immed_bw_main                     []
% 2.22/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.22/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/0.99  
% 2.22/0.99  ------ Combination Options
% 2.22/0.99  
% 2.22/0.99  --comb_res_mult                         3
% 2.22/0.99  --comb_sup_mult                         2
% 2.22/0.99  --comb_inst_mult                        10
% 2.22/0.99  
% 2.22/0.99  ------ Debug Options
% 2.22/0.99  
% 2.22/0.99  --dbg_backtrace                         false
% 2.22/0.99  --dbg_dump_prop_clauses                 false
% 2.22/0.99  --dbg_dump_prop_clauses_file            -
% 2.22/0.99  --dbg_out_stat                          false
% 2.22/0.99  ------ Parsing...
% 2.22/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.22/0.99  
% 2.22/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.22/0.99  
% 2.22/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.22/0.99  
% 2.22/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.22/0.99  ------ Proving...
% 2.22/0.99  ------ Problem Properties 
% 2.22/0.99  
% 2.22/0.99  
% 2.22/0.99  clauses                                 20
% 2.22/0.99  conjectures                             3
% 2.22/0.99  EPR                                     0
% 2.22/0.99  Horn                                    17
% 2.22/0.99  unary                                   5
% 2.22/0.99  binary                                  1
% 2.22/0.99  lits                                    71
% 2.22/0.99  lits eq                                 9
% 2.22/0.99  fd_pure                                 0
% 2.22/0.99  fd_pseudo                               0
% 2.22/0.99  fd_cond                                 0
% 2.22/0.99  fd_pseudo_cond                          6
% 2.22/0.99  AC symbols                              0
% 2.22/0.99  
% 2.22/0.99  ------ Schedule dynamic 5 is on 
% 2.22/0.99  
% 2.22/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.22/0.99  
% 2.22/0.99  
% 2.22/0.99  ------ 
% 2.22/0.99  Current options:
% 2.22/0.99  ------ 
% 2.22/0.99  
% 2.22/0.99  ------ Input Options
% 2.22/0.99  
% 2.22/0.99  --out_options                           all
% 2.22/0.99  --tptp_safe_out                         true
% 2.22/0.99  --problem_path                          ""
% 2.22/0.99  --include_path                          ""
% 2.22/0.99  --clausifier                            res/vclausify_rel
% 2.22/0.99  --clausifier_options                    --mode clausify
% 2.22/0.99  --stdin                                 false
% 2.22/0.99  --stats_out                             all
% 2.22/0.99  
% 2.22/0.99  ------ General Options
% 2.22/0.99  
% 2.22/0.99  --fof                                   false
% 2.22/0.99  --time_out_real                         305.
% 2.22/0.99  --time_out_virtual                      -1.
% 2.22/0.99  --symbol_type_check                     false
% 2.22/0.99  --clausify_out                          false
% 2.22/0.99  --sig_cnt_out                           false
% 2.22/0.99  --trig_cnt_out                          false
% 2.22/0.99  --trig_cnt_out_tolerance                1.
% 2.22/0.99  --trig_cnt_out_sk_spl                   false
% 2.22/0.99  --abstr_cl_out                          false
% 2.22/0.99  
% 2.22/0.99  ------ Global Options
% 2.22/0.99  
% 2.22/0.99  --schedule                              default
% 2.22/0.99  --add_important_lit                     false
% 2.22/0.99  --prop_solver_per_cl                    1000
% 2.22/0.99  --min_unsat_core                        false
% 2.22/0.99  --soft_assumptions                      false
% 2.22/0.99  --soft_lemma_size                       3
% 2.22/0.99  --prop_impl_unit_size                   0
% 2.22/0.99  --prop_impl_unit                        []
% 2.22/0.99  --share_sel_clauses                     true
% 2.22/0.99  --reset_solvers                         false
% 2.22/0.99  --bc_imp_inh                            [conj_cone]
% 2.22/0.99  --conj_cone_tolerance                   3.
% 2.22/0.99  --extra_neg_conj                        none
% 2.22/0.99  --large_theory_mode                     true
% 2.22/0.99  --prolific_symb_bound                   200
% 2.22/0.99  --lt_threshold                          2000
% 2.22/0.99  --clause_weak_htbl                      true
% 2.22/0.99  --gc_record_bc_elim                     false
% 2.22/0.99  
% 2.22/0.99  ------ Preprocessing Options
% 2.22/0.99  
% 2.22/0.99  --preprocessing_flag                    true
% 2.22/0.99  --time_out_prep_mult                    0.1
% 2.22/0.99  --splitting_mode                        input
% 2.22/0.99  --splitting_grd                         true
% 2.22/0.99  --splitting_cvd                         false
% 2.22/0.99  --splitting_cvd_svl                     false
% 2.22/0.99  --splitting_nvd                         32
% 2.22/0.99  --sub_typing                            true
% 2.22/0.99  --prep_gs_sim                           true
% 2.22/0.99  --prep_unflatten                        true
% 2.22/0.99  --prep_res_sim                          true
% 2.22/0.99  --prep_upred                            true
% 2.22/0.99  --prep_sem_filter                       exhaustive
% 2.22/0.99  --prep_sem_filter_out                   false
% 2.22/0.99  --pred_elim                             true
% 2.22/0.99  --res_sim_input                         true
% 2.22/0.99  --eq_ax_congr_red                       true
% 2.22/0.99  --pure_diseq_elim                       true
% 2.22/0.99  --brand_transform                       false
% 2.22/0.99  --non_eq_to_eq                          false
% 2.22/0.99  --prep_def_merge                        true
% 2.22/0.99  --prep_def_merge_prop_impl              false
% 2.22/0.99  --prep_def_merge_mbd                    true
% 2.22/0.99  --prep_def_merge_tr_red                 false
% 2.22/0.99  --prep_def_merge_tr_cl                  false
% 2.22/0.99  --smt_preprocessing                     true
% 2.22/0.99  --smt_ac_axioms                         fast
% 2.22/0.99  --preprocessed_out                      false
% 2.22/0.99  --preprocessed_stats                    false
% 2.22/0.99  
% 2.22/0.99  ------ Abstraction refinement Options
% 2.22/0.99  
% 2.22/0.99  --abstr_ref                             []
% 2.22/0.99  --abstr_ref_prep                        false
% 2.22/0.99  --abstr_ref_until_sat                   false
% 2.22/0.99  --abstr_ref_sig_restrict                funpre
% 2.22/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.22/0.99  --abstr_ref_under                       []
% 2.22/0.99  
% 2.22/0.99  ------ SAT Options
% 2.22/0.99  
% 2.22/0.99  --sat_mode                              false
% 2.22/0.99  --sat_fm_restart_options                ""
% 2.22/0.99  --sat_gr_def                            false
% 2.22/0.99  --sat_epr_types                         true
% 2.22/0.99  --sat_non_cyclic_types                  false
% 2.22/0.99  --sat_finite_models                     false
% 2.22/0.99  --sat_fm_lemmas                         false
% 2.22/0.99  --sat_fm_prep                           false
% 2.22/0.99  --sat_fm_uc_incr                        true
% 2.22/0.99  --sat_out_model                         small
% 2.22/0.99  --sat_out_clauses                       false
% 2.22/0.99  
% 2.22/0.99  ------ QBF Options
% 2.22/0.99  
% 2.22/0.99  --qbf_mode                              false
% 2.22/0.99  --qbf_elim_univ                         false
% 2.22/0.99  --qbf_dom_inst                          none
% 2.22/0.99  --qbf_dom_pre_inst                      false
% 2.22/0.99  --qbf_sk_in                             false
% 2.22/0.99  --qbf_pred_elim                         true
% 2.22/0.99  --qbf_split                             512
% 2.22/0.99  
% 2.22/0.99  ------ BMC1 Options
% 2.22/0.99  
% 2.22/0.99  --bmc1_incremental                      false
% 2.22/0.99  --bmc1_axioms                           reachable_all
% 2.22/0.99  --bmc1_min_bound                        0
% 2.22/0.99  --bmc1_max_bound                        -1
% 2.22/0.99  --bmc1_max_bound_default                -1
% 2.22/0.99  --bmc1_symbol_reachability              true
% 2.22/0.99  --bmc1_property_lemmas                  false
% 2.22/0.99  --bmc1_k_induction                      false
% 2.22/0.99  --bmc1_non_equiv_states                 false
% 2.22/0.99  --bmc1_deadlock                         false
% 2.22/0.99  --bmc1_ucm                              false
% 2.22/0.99  --bmc1_add_unsat_core                   none
% 2.22/0.99  --bmc1_unsat_core_children              false
% 2.22/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.22/0.99  --bmc1_out_stat                         full
% 2.22/0.99  --bmc1_ground_init                      false
% 2.22/0.99  --bmc1_pre_inst_next_state              false
% 2.22/0.99  --bmc1_pre_inst_state                   false
% 2.22/0.99  --bmc1_pre_inst_reach_state             false
% 2.22/0.99  --bmc1_out_unsat_core                   false
% 2.22/0.99  --bmc1_aig_witness_out                  false
% 2.22/0.99  --bmc1_verbose                          false
% 2.22/0.99  --bmc1_dump_clauses_tptp                false
% 2.22/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.22/0.99  --bmc1_dump_file                        -
% 2.22/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.22/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.22/0.99  --bmc1_ucm_extend_mode                  1
% 2.22/0.99  --bmc1_ucm_init_mode                    2
% 2.22/0.99  --bmc1_ucm_cone_mode                    none
% 2.22/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.22/0.99  --bmc1_ucm_relax_model                  4
% 2.22/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.22/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.22/0.99  --bmc1_ucm_layered_model                none
% 2.22/0.99  --bmc1_ucm_max_lemma_size               10
% 2.22/0.99  
% 2.22/0.99  ------ AIG Options
% 2.22/0.99  
% 2.22/0.99  --aig_mode                              false
% 2.22/0.99  
% 2.22/0.99  ------ Instantiation Options
% 2.22/0.99  
% 2.22/0.99  --instantiation_flag                    true
% 2.22/0.99  --inst_sos_flag                         false
% 2.22/0.99  --inst_sos_phase                        true
% 2.22/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.22/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.22/0.99  --inst_lit_sel_side                     none
% 2.22/0.99  --inst_solver_per_active                1400
% 2.22/0.99  --inst_solver_calls_frac                1.
% 2.22/0.99  --inst_passive_queue_type               priority_queues
% 2.22/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.22/0.99  --inst_passive_queues_freq              [25;2]
% 2.22/0.99  --inst_dismatching                      true
% 2.22/0.99  --inst_eager_unprocessed_to_passive     true
% 2.22/0.99  --inst_prop_sim_given                   true
% 2.22/0.99  --inst_prop_sim_new                     false
% 2.22/0.99  --inst_subs_new                         false
% 2.22/0.99  --inst_eq_res_simp                      false
% 2.22/0.99  --inst_subs_given                       false
% 2.22/0.99  --inst_orphan_elimination               true
% 2.22/0.99  --inst_learning_loop_flag               true
% 2.22/0.99  --inst_learning_start                   3000
% 2.22/0.99  --inst_learning_factor                  2
% 2.22/0.99  --inst_start_prop_sim_after_learn       3
% 2.22/0.99  --inst_sel_renew                        solver
% 2.22/0.99  --inst_lit_activity_flag                true
% 2.22/0.99  --inst_restr_to_given                   false
% 2.22/0.99  --inst_activity_threshold               500
% 2.22/0.99  --inst_out_proof                        true
% 2.22/0.99  
% 2.22/0.99  ------ Resolution Options
% 2.22/0.99  
% 2.22/0.99  --resolution_flag                       false
% 2.22/0.99  --res_lit_sel                           adaptive
% 2.22/0.99  --res_lit_sel_side                      none
% 2.22/0.99  --res_ordering                          kbo
% 2.22/0.99  --res_to_prop_solver                    active
% 2.22/0.99  --res_prop_simpl_new                    false
% 2.22/0.99  --res_prop_simpl_given                  true
% 2.22/0.99  --res_passive_queue_type                priority_queues
% 2.22/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.22/0.99  --res_passive_queues_freq               [15;5]
% 2.22/0.99  --res_forward_subs                      full
% 2.22/0.99  --res_backward_subs                     full
% 2.22/0.99  --res_forward_subs_resolution           true
% 2.22/0.99  --res_backward_subs_resolution          true
% 2.22/0.99  --res_orphan_elimination                true
% 2.22/0.99  --res_time_limit                        2.
% 2.22/0.99  --res_out_proof                         true
% 2.22/0.99  
% 2.22/0.99  ------ Superposition Options
% 2.22/0.99  
% 2.22/0.99  --superposition_flag                    true
% 2.22/0.99  --sup_passive_queue_type                priority_queues
% 2.22/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.22/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.22/0.99  --demod_completeness_check              fast
% 2.22/0.99  --demod_use_ground                      true
% 2.22/0.99  --sup_to_prop_solver                    passive
% 2.22/0.99  --sup_prop_simpl_new                    true
% 2.22/0.99  --sup_prop_simpl_given                  true
% 2.22/0.99  --sup_fun_splitting                     false
% 2.22/0.99  --sup_smt_interval                      50000
% 2.22/0.99  
% 2.22/0.99  ------ Superposition Simplification Setup
% 2.22/0.99  
% 2.22/0.99  --sup_indices_passive                   []
% 2.22/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.22/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/0.99  --sup_full_bw                           [BwDemod]
% 2.22/0.99  --sup_immed_triv                        [TrivRules]
% 2.22/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.22/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/0.99  --sup_immed_bw_main                     []
% 2.22/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.22/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/0.99  
% 2.22/0.99  ------ Combination Options
% 2.22/0.99  
% 2.22/0.99  --comb_res_mult                         3
% 2.22/0.99  --comb_sup_mult                         2
% 2.22/0.99  --comb_inst_mult                        10
% 2.22/0.99  
% 2.22/0.99  ------ Debug Options
% 2.22/0.99  
% 2.22/0.99  --dbg_backtrace                         false
% 2.22/0.99  --dbg_dump_prop_clauses                 false
% 2.22/0.99  --dbg_dump_prop_clauses_file            -
% 2.22/0.99  --dbg_out_stat                          false
% 2.22/0.99  
% 2.22/0.99  
% 2.22/0.99  
% 2.22/0.99  
% 2.22/0.99  ------ Proving...
% 2.22/0.99  
% 2.22/0.99  
% 2.22/0.99  % SZS status Theorem for theBenchmark.p
% 2.22/0.99  
% 2.22/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.22/0.99  
% 2.22/0.99  fof(f1,axiom,(
% 2.22/0.99    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 2.22/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.99  
% 2.22/0.99  fof(f16,plain,(
% 2.22/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 2.22/0.99    inference(ennf_transformation,[],[f1])).
% 2.22/0.99  
% 2.22/0.99  fof(f17,plain,(
% 2.22/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 2.22/0.99    inference(flattening,[],[f16])).
% 2.22/0.99  
% 2.22/0.99  fof(f44,plain,(
% 2.22/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.22/0.99    inference(cnf_transformation,[],[f17])).
% 2.22/0.99  
% 2.22/0.99  fof(f13,conjecture,(
% 2.22/0.99    ! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 2.22/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.99  
% 2.22/0.99  fof(f14,negated_conjecture,(
% 2.22/0.99    ~! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 2.22/0.99    inference(negated_conjecture,[],[f13])).
% 2.22/0.99  
% 2.22/0.99  fof(f31,plain,(
% 2.22/0.99    ? [X0] : ((? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0))) & ~v1_xboole_0(X0))),
% 2.22/0.99    inference(ennf_transformation,[],[f14])).
% 2.22/0.99  
% 2.22/0.99  fof(f32,plain,(
% 2.22/0.99    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0))),
% 2.22/0.99    inference(flattening,[],[f31])).
% 2.22/0.99  
% 2.22/0.99  fof(f42,plain,(
% 2.22/0.99    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) => (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,sK3),k3_xboole_0(X1,sK3)) & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0))))) )),
% 2.22/0.99    introduced(choice_axiom,[])).
% 2.22/0.99  
% 2.22/0.99  fof(f41,plain,(
% 2.22/0.99    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) => (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),sK2,X2),k3_xboole_0(sK2,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(X0))))) )),
% 2.22/0.99    introduced(choice_axiom,[])).
% 2.22/0.99  
% 2.22/0.99  fof(f40,plain,(
% 2.22/0.99    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK1),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK1)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))) & v2_lattice3(k2_yellow_1(sK1)) & ~v1_xboole_0(sK1))),
% 2.22/0.99    introduced(choice_axiom,[])).
% 2.22/0.99  
% 2.22/0.99  fof(f43,plain,(
% 2.22/0.99    ((~r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k3_xboole_0(sK2,sK3)) & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))) & v2_lattice3(k2_yellow_1(sK1)) & ~v1_xboole_0(sK1)),
% 2.22/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f32,f42,f41,f40])).
% 2.22/0.99  
% 2.22/0.99  fof(f72,plain,(
% 2.22/0.99    ~r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k3_xboole_0(sK2,sK3))),
% 2.22/0.99    inference(cnf_transformation,[],[f43])).
% 2.22/0.99  
% 2.22/0.99  fof(f9,axiom,(
% 2.22/0.99    ! [X0] : g1_orders_2(X0,k1_yellow_1(X0)) = k2_yellow_1(X0)),
% 2.22/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.99  
% 2.22/0.99  fof(f60,plain,(
% 2.22/0.99    ( ! [X0] : (g1_orders_2(X0,k1_yellow_1(X0)) = k2_yellow_1(X0)) )),
% 2.22/0.99    inference(cnf_transformation,[],[f9])).
% 2.22/0.99  
% 2.22/0.99  fof(f80,plain,(
% 2.22/0.99    ~r1_tarski(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),k3_xboole_0(sK2,sK3))),
% 2.22/0.99    inference(definition_unfolding,[],[f72,f60])).
% 2.22/0.99  
% 2.22/0.99  fof(f7,axiom,(
% 2.22/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 2.22/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.99  
% 2.22/0.99  fof(f26,plain,(
% 2.22/0.99    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 2.22/0.99    inference(ennf_transformation,[],[f7])).
% 2.22/0.99  
% 2.22/0.99  fof(f27,plain,(
% 2.22/0.99    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 2.22/0.99    inference(flattening,[],[f26])).
% 2.22/0.99  
% 2.22/0.99  fof(f52,plain,(
% 2.22/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.22/0.99    inference(cnf_transformation,[],[f27])).
% 2.22/0.99  
% 2.22/0.99  fof(f5,axiom,(
% 2.22/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 2.22/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.99  
% 2.22/0.99  fof(f22,plain,(
% 2.22/0.99    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.22/0.99    inference(ennf_transformation,[],[f5])).
% 2.22/0.99  
% 2.22/0.99  fof(f23,plain,(
% 2.22/0.99    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.22/0.99    inference(flattening,[],[f22])).
% 2.22/0.99  
% 2.22/0.99  fof(f33,plain,(
% 2.22/0.99    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.22/0.99    inference(nnf_transformation,[],[f23])).
% 2.22/0.99  
% 2.22/0.99  fof(f50,plain,(
% 2.22/0.99    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.22/0.99    inference(cnf_transformation,[],[f33])).
% 2.22/0.99  
% 2.22/0.99  fof(f6,axiom,(
% 2.22/0.99    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 2.22/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.99  
% 2.22/0.99  fof(f24,plain,(
% 2.22/0.99    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 2.22/0.99    inference(ennf_transformation,[],[f6])).
% 2.22/0.99  
% 2.22/0.99  fof(f25,plain,(
% 2.22/0.99    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 2.22/0.99    inference(flattening,[],[f24])).
% 2.22/0.99  
% 2.22/0.99  fof(f51,plain,(
% 2.22/0.99    ( ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0)) )),
% 2.22/0.99    inference(cnf_transformation,[],[f25])).
% 2.22/0.99  
% 2.22/0.99  fof(f12,axiom,(
% 2.22/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 2.22/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.99  
% 2.22/0.99  fof(f30,plain,(
% 2.22/0.99    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 2.22/0.99    inference(ennf_transformation,[],[f12])).
% 2.22/0.99  
% 2.22/0.99  fof(f39,plain,(
% 2.22/0.99    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 2.22/0.99    inference(nnf_transformation,[],[f30])).
% 2.22/0.99  
% 2.22/0.99  fof(f66,plain,(
% 2.22/0.99    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 2.22/0.99    inference(cnf_transformation,[],[f39])).
% 2.22/0.99  
% 2.22/0.99  fof(f79,plain,(
% 2.22/0.99    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2) | ~m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | v1_xboole_0(X0)) )),
% 2.22/0.99    inference(definition_unfolding,[],[f66,f60,f60,f60])).
% 2.22/0.99  
% 2.22/0.99  fof(f68,plain,(
% 2.22/0.99    ~v1_xboole_0(sK1)),
% 2.22/0.99    inference(cnf_transformation,[],[f43])).
% 2.22/0.99  
% 2.22/0.99  fof(f69,plain,(
% 2.22/0.99    v2_lattice3(k2_yellow_1(sK1))),
% 2.22/0.99    inference(cnf_transformation,[],[f43])).
% 2.22/0.99  
% 2.22/0.99  fof(f83,plain,(
% 2.22/0.99    v2_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)))),
% 2.22/0.99    inference(definition_unfolding,[],[f69,f60])).
% 2.22/0.99  
% 2.22/0.99  fof(f11,axiom,(
% 2.22/0.99    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 2.22/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.99  
% 2.22/0.99  fof(f15,plain,(
% 2.22/0.99    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 2.22/0.99    inference(pure_predicate_removal,[],[f11])).
% 2.22/0.99  
% 2.22/0.99  fof(f64,plain,(
% 2.22/0.99    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 2.22/0.99    inference(cnf_transformation,[],[f15])).
% 2.22/0.99  
% 2.22/0.99  fof(f76,plain,(
% 2.22/0.99    ( ! [X0] : (v3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) )),
% 2.22/0.99    inference(definition_unfolding,[],[f64,f60])).
% 2.22/0.99  
% 2.22/0.99  fof(f10,axiom,(
% 2.22/0.99    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 2.22/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.99  
% 2.22/0.99  fof(f62,plain,(
% 2.22/0.99    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 2.22/0.99    inference(cnf_transformation,[],[f10])).
% 2.22/0.99  
% 2.22/0.99  fof(f73,plain,(
% 2.22/0.99    ( ! [X0] : (l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) )),
% 2.22/0.99    inference(definition_unfolding,[],[f62,f60])).
% 2.22/0.99  
% 2.22/0.99  fof(f8,axiom,(
% 2.22/0.99    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 2.22/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.99  
% 2.22/0.99  fof(f28,plain,(
% 2.22/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 2.22/0.99    inference(ennf_transformation,[],[f8])).
% 2.22/0.99  
% 2.22/0.99  fof(f29,plain,(
% 2.22/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.22/0.99    inference(flattening,[],[f28])).
% 2.22/0.99  
% 2.22/0.99  fof(f34,plain,(
% 2.22/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.22/0.99    inference(nnf_transformation,[],[f29])).
% 2.22/0.99  
% 2.22/0.99  fof(f35,plain,(
% 2.22/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.22/0.99    inference(flattening,[],[f34])).
% 2.22/0.99  
% 2.22/0.99  fof(f36,plain,(
% 2.22/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.22/0.99    inference(rectify,[],[f35])).
% 2.22/0.99  
% 2.22/0.99  fof(f37,plain,(
% 2.22/0.99    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK0(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK0(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK0(X0,X1,X2,X3),X1) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))))),
% 2.22/0.99    introduced(choice_axiom,[])).
% 2.22/0.99  
% 2.22/0.99  fof(f38,plain,(
% 2.22/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,sK0(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK0(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK0(X0,X1,X2,X3),X1) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.22/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).
% 2.22/0.99  
% 2.22/0.99  fof(f53,plain,(
% 2.22/0.99    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X3,X1) | k11_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.22/0.99    inference(cnf_transformation,[],[f38])).
% 2.22/0.99  
% 2.22/0.99  fof(f86,plain,(
% 2.22/0.99    ( ! [X2,X0,X1] : (r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1) | ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.22/0.99    inference(equality_resolution,[],[f53])).
% 2.22/0.99  
% 2.22/0.99  fof(f65,plain,(
% 2.22/0.99    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 2.22/0.99    inference(cnf_transformation,[],[f15])).
% 2.22/0.99  
% 2.22/0.99  fof(f75,plain,(
% 2.22/0.99    ( ! [X0] : (v5_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) )),
% 2.22/0.99    inference(definition_unfolding,[],[f65,f60])).
% 2.22/0.99  
% 2.22/0.99  fof(f54,plain,(
% 2.22/0.99    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X3,X2) | k11_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.22/0.99    inference(cnf_transformation,[],[f38])).
% 2.22/0.99  
% 2.22/0.99  fof(f85,plain,(
% 2.22/0.99    ( ! [X2,X0,X1] : (r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2) | ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.22/0.99    inference(equality_resolution,[],[f54])).
% 2.22/0.99  
% 2.22/0.99  fof(f71,plain,(
% 2.22/0.99    m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))),
% 2.22/0.99    inference(cnf_transformation,[],[f43])).
% 2.22/0.99  
% 2.22/0.99  fof(f81,plain,(
% 2.22/0.99    m1_subset_1(sK3,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))),
% 2.22/0.99    inference(definition_unfolding,[],[f71,f60])).
% 2.22/0.99  
% 2.22/0.99  fof(f70,plain,(
% 2.22/0.99    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))),
% 2.22/0.99    inference(cnf_transformation,[],[f43])).
% 2.22/0.99  
% 2.22/0.99  fof(f82,plain,(
% 2.22/0.99    m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))),
% 2.22/0.99    inference(definition_unfolding,[],[f70,f60])).
% 2.22/0.99  
% 2.22/0.99  cnf(c_0,plain,
% 2.22/0.99      ( ~ r1_tarski(X0,X1)
% 2.22/0.99      | ~ r1_tarski(X0,X2)
% 2.22/0.99      | r1_tarski(X0,k3_xboole_0(X2,X1)) ),
% 2.22/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1537,plain,
% 2.22/0.99      ( r1_tarski(X0,X1) != iProver_top
% 2.22/0.99      | r1_tarski(X0,X2) != iProver_top
% 2.22/0.99      | r1_tarski(X0,k3_xboole_0(X2,X1)) = iProver_top ),
% 2.22/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_23,negated_conjecture,
% 2.22/0.99      ( ~ r1_tarski(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),k3_xboole_0(sK2,sK3)) ),
% 2.22/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1529,plain,
% 2.22/0.99      ( r1_tarski(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),k3_xboole_0(sK2,sK3)) != iProver_top ),
% 2.22/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_2696,plain,
% 2.22/0.99      ( r1_tarski(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),sK3) != iProver_top
% 2.22/0.99      | r1_tarski(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),sK2) != iProver_top ),
% 2.22/0.99      inference(superposition,[status(thm)],[c_1537,c_1529]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_8,plain,
% 2.22/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.22/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.22/0.99      | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
% 2.22/0.99      | ~ l1_orders_2(X1) ),
% 2.22/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1850,plain,
% 2.22/0.99      ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))
% 2.22/0.99      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))
% 2.22/0.99      | m1_subset_1(k11_lattice3(g1_orders_2(X1,k1_yellow_1(X1)),X2,X0),u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))
% 2.22/0.99      | ~ l1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ),
% 2.22/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_2241,plain,
% 2.22/0.99      ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | m1_subset_1(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,sK3),u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | ~ m1_subset_1(sK3,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | ~ l1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1))) ),
% 2.22/0.99      inference(instantiation,[status(thm)],[c_1850]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_2597,plain,
% 2.22/0.99      ( m1_subset_1(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | ~ m1_subset_1(sK3,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | ~ m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | ~ l1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1))) ),
% 2.22/0.99      inference(instantiation,[status(thm)],[c_2241]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_2598,plain,
% 2.22/0.99      ( m1_subset_1(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) = iProver_top
% 2.22/0.99      | m1_subset_1(sK3,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) != iProver_top
% 2.22/0.99      | m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) != iProver_top
% 2.22/0.99      | l1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1))) != iProver_top ),
% 2.22/0.99      inference(predicate_to_equality,[status(thm)],[c_2597]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_5,plain,
% 2.22/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 2.22/0.99      | r3_orders_2(X0,X1,X2)
% 2.22/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.22/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.22/0.99      | v2_struct_0(X0)
% 2.22/0.99      | ~ v3_orders_2(X0)
% 2.22/0.99      | ~ l1_orders_2(X0) ),
% 2.22/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_7,plain,
% 2.22/0.99      ( ~ v2_lattice3(X0) | ~ v2_struct_0(X0) | ~ l1_orders_2(X0) ),
% 2.22/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_493,plain,
% 2.22/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 2.22/0.99      | r3_orders_2(X0,X1,X2)
% 2.22/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.22/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.22/0.99      | ~ v2_lattice3(X0)
% 2.22/0.99      | ~ v3_orders_2(X0)
% 2.22/0.99      | ~ l1_orders_2(X0) ),
% 2.22/0.99      inference(resolution,[status(thm)],[c_5,c_7]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_22,plain,
% 2.22/0.99      ( ~ r3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2)
% 2.22/0.99      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
% 2.22/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
% 2.22/0.99      | r1_tarski(X1,X2)
% 2.22/0.99      | v1_xboole_0(X0) ),
% 2.22/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_27,negated_conjecture,
% 2.22/0.99      ( ~ v1_xboole_0(sK1) ),
% 2.22/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_357,plain,
% 2.22/0.99      ( ~ r3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2)
% 2.22/0.99      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
% 2.22/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
% 2.22/0.99      | r1_tarski(X1,X2)
% 2.22/0.99      | sK1 != X0 ),
% 2.22/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_27]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_358,plain,
% 2.22/0.99      ( ~ r3_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,X1)
% 2.22/0.99      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | r1_tarski(X0,X1) ),
% 2.22/0.99      inference(unflattening,[status(thm)],[c_357]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_601,plain,
% 2.22/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 2.22/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.22/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.22/0.99      | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | ~ m1_subset_1(X4,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | r1_tarski(X3,X4)
% 2.22/0.99      | ~ v2_lattice3(X0)
% 2.22/0.99      | ~ v3_orders_2(X0)
% 2.22/0.99      | ~ l1_orders_2(X0)
% 2.22/0.99      | X3 != X1
% 2.22/0.99      | X4 != X2
% 2.22/0.99      | g1_orders_2(sK1,k1_yellow_1(sK1)) != X0 ),
% 2.22/0.99      inference(resolution_lifted,[status(thm)],[c_493,c_358]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_602,plain,
% 2.22/0.99      ( ~ r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,X1)
% 2.22/0.99      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | r1_tarski(X0,X1)
% 2.22/0.99      | ~ v2_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)))
% 2.22/0.99      | ~ v3_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)))
% 2.22/0.99      | ~ l1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1))) ),
% 2.22/0.99      inference(unflattening,[status(thm)],[c_601]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_26,negated_conjecture,
% 2.22/0.99      ( v2_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1))) ),
% 2.22/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_19,plain,
% 2.22/0.99      ( v3_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
% 2.22/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_43,plain,
% 2.22/0.99      ( v3_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1))) ),
% 2.22/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_16,plain,
% 2.22/0.99      ( l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
% 2.22/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_50,plain,
% 2.22/0.99      ( l1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1))) ),
% 2.22/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_606,plain,
% 2.22/0.99      ( r1_tarski(X0,X1)
% 2.22/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | ~ r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,X1) ),
% 2.22/0.99      inference(global_propositional_subsumption,
% 2.22/0.99                [status(thm)],
% 2.22/0.99                [c_602,c_26,c_43,c_50]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_607,plain,
% 2.22/0.99      ( ~ r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,X1)
% 2.22/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | r1_tarski(X0,X1) ),
% 2.22/0.99      inference(renaming,[status(thm)],[c_606]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1790,plain,
% 2.22/0.99      ( ~ r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,sK2)
% 2.22/0.99      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | ~ m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | r1_tarski(X0,sK2) ),
% 2.22/0.99      inference(instantiation,[status(thm)],[c_607]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_2314,plain,
% 2.22/0.99      ( ~ r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),sK2)
% 2.22/0.99      | ~ m1_subset_1(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | ~ m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | r1_tarski(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),sK2) ),
% 2.22/0.99      inference(instantiation,[status(thm)],[c_1790]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_2320,plain,
% 2.22/0.99      ( r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),sK2) != iProver_top
% 2.22/0.99      | m1_subset_1(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) != iProver_top
% 2.22/0.99      | m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) != iProver_top
% 2.22/0.99      | r1_tarski(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),sK2) = iProver_top ),
% 2.22/0.99      inference(predicate_to_equality,[status(thm)],[c_2314]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1785,plain,
% 2.22/0.99      ( ~ r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,sK3)
% 2.22/0.99      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | ~ m1_subset_1(sK3,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | r1_tarski(X0,sK3) ),
% 2.22/0.99      inference(instantiation,[status(thm)],[c_607]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_2285,plain,
% 2.22/0.99      ( ~ r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),sK3)
% 2.22/0.99      | ~ m1_subset_1(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | ~ m1_subset_1(sK3,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | r1_tarski(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),sK3) ),
% 2.22/0.99      inference(instantiation,[status(thm)],[c_1785]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_2291,plain,
% 2.22/0.99      ( r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),sK3) != iProver_top
% 2.22/0.99      | m1_subset_1(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) != iProver_top
% 2.22/0.99      | m1_subset_1(sK3,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) != iProver_top
% 2.22/0.99      | r1_tarski(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),sK3) = iProver_top ),
% 2.22/0.99      inference(predicate_to_equality,[status(thm)],[c_2285]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_931,plain,
% 2.22/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.22/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.22/0.99      | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
% 2.22/0.99      | g1_orders_2(X3,k1_yellow_1(X3)) != X1 ),
% 2.22/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_16]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_932,plain,
% 2.22/0.99      ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))
% 2.22/0.99      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))
% 2.22/0.99      | m1_subset_1(k11_lattice3(g1_orders_2(X1,k1_yellow_1(X1)),X0,X2),u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1)))) ),
% 2.22/0.99      inference(unflattening,[status(thm)],[c_931]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_15,plain,
% 2.22/0.99      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
% 2.22/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.22/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.22/0.99      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.22/0.99      | ~ v5_orders_2(X0)
% 2.22/0.99      | ~ v2_lattice3(X0)
% 2.22/0.99      | v2_struct_0(X0)
% 2.22/0.99      | ~ l1_orders_2(X0) ),
% 2.22/0.99      inference(cnf_transformation,[],[f86]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_163,plain,
% 2.22/0.99      ( ~ v2_lattice3(X0)
% 2.22/0.99      | ~ v5_orders_2(X0)
% 2.22/0.99      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.22/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.22/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.22/0.99      | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
% 2.22/0.99      | ~ l1_orders_2(X0) ),
% 2.22/0.99      inference(global_propositional_subsumption,
% 2.22/0.99                [status(thm)],
% 2.22/0.99                [c_15,c_7]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_164,plain,
% 2.22/0.99      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
% 2.22/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.22/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.22/0.99      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.22/0.99      | ~ v5_orders_2(X0)
% 2.22/0.99      | ~ v2_lattice3(X0)
% 2.22/0.99      | ~ l1_orders_2(X0) ),
% 2.22/0.99      inference(renaming,[status(thm)],[c_163]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_844,plain,
% 2.22/0.99      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
% 2.22/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.22/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.22/0.99      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.22/0.99      | ~ v5_orders_2(X0)
% 2.22/0.99      | ~ l1_orders_2(X0)
% 2.22/0.99      | g1_orders_2(sK1,k1_yellow_1(sK1)) != X0 ),
% 2.22/0.99      inference(resolution_lifted,[status(thm)],[c_164,c_26]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_845,plain,
% 2.22/0.99      ( r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,X1),X0)
% 2.22/0.99      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | ~ m1_subset_1(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,X1),u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | ~ v5_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)))
% 2.22/0.99      | ~ l1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1))) ),
% 2.22/0.99      inference(unflattening,[status(thm)],[c_844]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_18,plain,
% 2.22/0.99      ( v5_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
% 2.22/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_46,plain,
% 2.22/0.99      ( v5_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1))) ),
% 2.22/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_847,plain,
% 2.22/0.99      ( r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,X1),X0)
% 2.22/0.99      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | ~ m1_subset_1(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,X1),u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) ),
% 2.22/0.99      inference(global_propositional_subsumption,
% 2.22/0.99                [status(thm)],
% 2.22/0.99                [c_845,c_46,c_50]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_848,plain,
% 2.22/0.99      ( r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,X1),X0)
% 2.22/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | ~ m1_subset_1(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,X1),u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) ),
% 2.22/0.99      inference(renaming,[status(thm)],[c_847]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_952,plain,
% 2.22/0.99      ( r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,X1),X0)
% 2.22/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) ),
% 2.22/0.99      inference(backward_subsumption_resolution,
% 2.22/0.99                [status(thm)],
% 2.22/0.99                [c_932,c_848]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1765,plain,
% 2.22/0.99      ( r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,sK3),X0)
% 2.22/0.99      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | ~ m1_subset_1(sK3,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) ),
% 2.22/0.99      inference(instantiation,[status(thm)],[c_952]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_2000,plain,
% 2.22/0.99      ( r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),sK2)
% 2.22/0.99      | ~ m1_subset_1(sK3,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | ~ m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) ),
% 2.22/0.99      inference(instantiation,[status(thm)],[c_1765]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_2001,plain,
% 2.22/0.99      ( r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),sK2) = iProver_top
% 2.22/0.99      | m1_subset_1(sK3,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) != iProver_top
% 2.22/0.99      | m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) != iProver_top ),
% 2.22/0.99      inference(predicate_to_equality,[status(thm)],[c_2000]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_14,plain,
% 2.22/0.99      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
% 2.22/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.22/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.22/0.99      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.22/0.99      | ~ v5_orders_2(X0)
% 2.22/0.99      | ~ v2_lattice3(X0)
% 2.22/0.99      | v2_struct_0(X0)
% 2.22/0.99      | ~ l1_orders_2(X0) ),
% 2.22/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_170,plain,
% 2.22/0.99      ( ~ v2_lattice3(X0)
% 2.22/0.99      | ~ v5_orders_2(X0)
% 2.22/0.99      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.22/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.22/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.22/0.99      | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
% 2.22/0.99      | ~ l1_orders_2(X0) ),
% 2.22/0.99      inference(global_propositional_subsumption,
% 2.22/0.99                [status(thm)],
% 2.22/0.99                [c_14,c_7]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_171,plain,
% 2.22/0.99      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
% 2.22/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.22/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.22/0.99      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.22/0.99      | ~ v5_orders_2(X0)
% 2.22/0.99      | ~ v2_lattice3(X0)
% 2.22/0.99      | ~ l1_orders_2(X0) ),
% 2.22/0.99      inference(renaming,[status(thm)],[c_170]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_820,plain,
% 2.22/0.99      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
% 2.22/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.22/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.22/0.99      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.22/0.99      | ~ v5_orders_2(X0)
% 2.22/0.99      | ~ l1_orders_2(X0)
% 2.22/0.99      | g1_orders_2(sK1,k1_yellow_1(sK1)) != X0 ),
% 2.22/0.99      inference(resolution_lifted,[status(thm)],[c_171,c_26]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_821,plain,
% 2.22/0.99      ( r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,X1),X1)
% 2.22/0.99      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | ~ m1_subset_1(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,X1),u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | ~ v5_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)))
% 2.22/0.99      | ~ l1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1))) ),
% 2.22/0.99      inference(unflattening,[status(thm)],[c_820]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_825,plain,
% 2.22/0.99      ( r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,X1),X1)
% 2.22/0.99      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | ~ m1_subset_1(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,X1),u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) ),
% 2.22/0.99      inference(global_propositional_subsumption,
% 2.22/0.99                [status(thm)],
% 2.22/0.99                [c_821,c_46,c_50]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_826,plain,
% 2.22/0.99      ( r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,X1),X1)
% 2.22/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | ~ m1_subset_1(k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,X1),u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) ),
% 2.22/0.99      inference(renaming,[status(thm)],[c_825]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_953,plain,
% 2.22/0.99      ( r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,X1),X1)
% 2.22/0.99      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) ),
% 2.22/0.99      inference(backward_subsumption_resolution,
% 2.22/0.99                [status(thm)],
% 2.22/0.99                [c_932,c_826]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1775,plain,
% 2.22/0.99      ( r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),X0,sK3),sK3)
% 2.22/0.99      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | ~ m1_subset_1(sK3,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) ),
% 2.22/0.99      inference(instantiation,[status(thm)],[c_953]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1996,plain,
% 2.22/0.99      ( r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),sK3)
% 2.22/0.99      | ~ m1_subset_1(sK3,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1))))
% 2.22/0.99      | ~ m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) ),
% 2.22/0.99      inference(instantiation,[status(thm)],[c_1775]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1997,plain,
% 2.22/0.99      ( r1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1)),k11_lattice3(g1_orders_2(sK1,k1_yellow_1(sK1)),sK2,sK3),sK3) = iProver_top
% 2.22/0.99      | m1_subset_1(sK3,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) != iProver_top
% 2.22/0.99      | m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) != iProver_top ),
% 2.22/0.99      inference(predicate_to_equality,[status(thm)],[c_1996]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_49,plain,
% 2.22/0.99      ( l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) = iProver_top ),
% 2.22/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_51,plain,
% 2.22/0.99      ( l1_orders_2(g1_orders_2(sK1,k1_yellow_1(sK1))) = iProver_top ),
% 2.22/0.99      inference(instantiation,[status(thm)],[c_49]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_24,negated_conjecture,
% 2.22/0.99      ( m1_subset_1(sK3,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) ),
% 2.22/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_31,plain,
% 2.22/0.99      ( m1_subset_1(sK3,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) = iProver_top ),
% 2.22/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_25,negated_conjecture,
% 2.22/0.99      ( m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) ),
% 2.22/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_30,plain,
% 2.22/0.99      ( m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK1,k1_yellow_1(sK1)))) = iProver_top ),
% 2.22/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(contradiction,plain,
% 2.22/0.99      ( $false ),
% 2.22/0.99      inference(minisat,
% 2.22/0.99                [status(thm)],
% 2.22/0.99                [c_2696,c_2598,c_2320,c_2291,c_2001,c_1997,c_51,c_31,
% 2.22/0.99                 c_30]) ).
% 2.22/0.99  
% 2.22/0.99  
% 2.22/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.22/0.99  
% 2.22/0.99  ------                               Statistics
% 2.22/0.99  
% 2.22/0.99  ------ General
% 2.22/0.99  
% 2.22/0.99  abstr_ref_over_cycles:                  0
% 2.22/0.99  abstr_ref_under_cycles:                 0
% 2.22/0.99  gc_basic_clause_elim:                   0
% 2.22/0.99  forced_gc_time:                         0
% 2.22/0.99  parsing_time:                           0.013
% 2.22/0.99  unif_index_cands_time:                  0.
% 2.22/0.99  unif_index_add_time:                    0.
% 2.22/0.99  orderings_time:                         0.
% 2.22/0.99  out_proof_time:                         0.012
% 2.22/0.99  total_time:                             0.135
% 2.22/0.99  num_of_symbols:                         54
% 2.22/0.99  num_of_terms:                           2336
% 2.22/0.99  
% 2.22/0.99  ------ Preprocessing
% 2.22/0.99  
% 2.22/0.99  num_of_splits:                          0
% 2.22/0.99  num_of_split_atoms:                     0
% 2.22/0.99  num_of_reused_defs:                     0
% 2.22/0.99  num_eq_ax_congr_red:                    17
% 2.22/0.99  num_of_sem_filtered_clauses:            1
% 2.22/0.99  num_of_subtypes:                        0
% 2.22/0.99  monotx_restored_types:                  0
% 2.22/0.99  sat_num_of_epr_types:                   0
% 2.22/0.99  sat_num_of_non_cyclic_types:            0
% 2.22/0.99  sat_guarded_non_collapsed_types:        0
% 2.22/0.99  num_pure_diseq_elim:                    0
% 2.22/0.99  simp_replaced_by:                       0
% 2.22/0.99  res_preprocessed:                       118
% 2.22/0.99  prep_upred:                             0
% 2.22/0.99  prep_unflattend:                        27
% 2.22/0.99  smt_new_axioms:                         0
% 2.22/0.99  pred_elim_cands:                        5
% 2.22/0.99  pred_elim:                              6
% 2.22/0.99  pred_elim_cl:                           7
% 2.22/0.99  pred_elim_cycles:                       13
% 2.22/0.99  merged_defs:                            0
% 2.22/0.99  merged_defs_ncl:                        0
% 2.22/0.99  bin_hyper_res:                          0
% 2.22/0.99  prep_cycles:                            4
% 2.22/0.99  pred_elim_time:                         0.017
% 2.22/0.99  splitting_time:                         0.
% 2.22/0.99  sem_filter_time:                        0.
% 2.22/0.99  monotx_time:                            0.001
% 2.22/0.99  subtype_inf_time:                       0.
% 2.22/0.99  
% 2.22/0.99  ------ Problem properties
% 2.22/0.99  
% 2.22/0.99  clauses:                                20
% 2.22/0.99  conjectures:                            3
% 2.22/0.99  epr:                                    0
% 2.22/0.99  horn:                                   17
% 2.22/0.99  ground:                                 3
% 2.22/0.99  unary:                                  5
% 2.22/0.99  binary:                                 1
% 2.22/0.99  lits:                                   71
% 2.22/0.99  lits_eq:                                9
% 2.22/0.99  fd_pure:                                0
% 2.22/0.99  fd_pseudo:                              0
% 2.22/0.99  fd_cond:                                0
% 2.22/0.99  fd_pseudo_cond:                         6
% 2.22/0.99  ac_symbols:                             0
% 2.22/0.99  
% 2.22/0.99  ------ Propositional Solver
% 2.22/0.99  
% 2.22/0.99  prop_solver_calls:                      25
% 2.22/0.99  prop_fast_solver_calls:                 1195
% 2.22/0.99  smt_solver_calls:                       0
% 2.22/0.99  smt_fast_solver_calls:                  0
% 2.22/0.99  prop_num_of_clauses:                    791
% 2.22/0.99  prop_preprocess_simplified:             4048
% 2.22/0.99  prop_fo_subsumed:                       35
% 2.22/0.99  prop_solver_time:                       0.
% 2.22/0.99  smt_solver_time:                        0.
% 2.22/0.99  smt_fast_solver_time:                   0.
% 2.22/0.99  prop_fast_solver_time:                  0.
% 2.22/0.99  prop_unsat_core_time:                   0.
% 2.22/0.99  
% 2.22/0.99  ------ QBF
% 2.22/0.99  
% 2.22/0.99  qbf_q_res:                              0
% 2.22/0.99  qbf_num_tautologies:                    0
% 2.22/0.99  qbf_prep_cycles:                        0
% 2.22/0.99  
% 2.22/0.99  ------ BMC1
% 2.22/0.99  
% 2.22/0.99  bmc1_current_bound:                     -1
% 2.22/0.99  bmc1_last_solved_bound:                 -1
% 2.22/0.99  bmc1_unsat_core_size:                   -1
% 2.22/0.99  bmc1_unsat_core_parents_size:           -1
% 2.22/0.99  bmc1_merge_next_fun:                    0
% 2.22/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.22/0.99  
% 2.22/0.99  ------ Instantiation
% 2.22/0.99  
% 2.22/0.99  inst_num_of_clauses:                    169
% 2.22/0.99  inst_num_in_passive:                    51
% 2.22/0.99  inst_num_in_active:                     109
% 2.22/0.99  inst_num_in_unprocessed:                9
% 2.22/0.99  inst_num_of_loops:                      120
% 2.22/0.99  inst_num_of_learning_restarts:          0
% 2.22/0.99  inst_num_moves_active_passive:          9
% 2.22/0.99  inst_lit_activity:                      0
% 2.22/0.99  inst_lit_activity_moves:                0
% 2.22/0.99  inst_num_tautologies:                   0
% 2.22/0.99  inst_num_prop_implied:                  0
% 2.22/0.99  inst_num_existing_simplified:           0
% 2.22/0.99  inst_num_eq_res_simplified:             0
% 2.22/0.99  inst_num_child_elim:                    0
% 2.22/0.99  inst_num_of_dismatching_blockings:      15
% 2.22/0.99  inst_num_of_non_proper_insts:           110
% 2.22/0.99  inst_num_of_duplicates:                 0
% 2.22/0.99  inst_inst_num_from_inst_to_res:         0
% 2.22/0.99  inst_dismatching_checking_time:         0.
% 2.22/0.99  
% 2.22/0.99  ------ Resolution
% 2.22/0.99  
% 2.22/0.99  res_num_of_clauses:                     0
% 2.22/0.99  res_num_in_passive:                     0
% 2.22/0.99  res_num_in_active:                      0
% 2.22/0.99  res_num_of_loops:                       122
% 2.22/0.99  res_forward_subset_subsumed:            4
% 2.22/0.99  res_backward_subset_subsumed:           0
% 2.22/0.99  res_forward_subsumed:                   0
% 2.22/0.99  res_backward_subsumed:                  0
% 2.22/0.99  res_forward_subsumption_resolution:     0
% 2.22/0.99  res_backward_subsumption_resolution:    3
% 2.22/0.99  res_clause_to_clause_subsumption:       140
% 2.22/0.99  res_orphan_elimination:                 0
% 2.22/0.99  res_tautology_del:                      6
% 2.22/0.99  res_num_eq_res_simplified:              0
% 2.22/0.99  res_num_sel_changes:                    0
% 2.22/0.99  res_moves_from_active_to_pass:          0
% 2.22/0.99  
% 2.22/0.99  ------ Superposition
% 2.22/0.99  
% 2.22/0.99  sup_time_total:                         0.
% 2.22/0.99  sup_time_generating:                    0.
% 2.22/0.99  sup_time_sim_full:                      0.
% 2.22/0.99  sup_time_sim_immed:                     0.
% 2.22/0.99  
% 2.22/0.99  sup_num_of_clauses:                     37
% 2.22/0.99  sup_num_in_active:                      23
% 2.22/0.99  sup_num_in_passive:                     14
% 2.22/0.99  sup_num_of_loops:                       22
% 2.22/0.99  sup_fw_superposition:                   13
% 2.22/0.99  sup_bw_superposition:                   4
% 2.22/0.99  sup_immediate_simplified:               0
% 2.22/0.99  sup_given_eliminated:                   0
% 2.22/0.99  comparisons_done:                       0
% 2.22/0.99  comparisons_avoided:                    0
% 2.22/0.99  
% 2.22/0.99  ------ Simplifications
% 2.22/0.99  
% 2.22/0.99  
% 2.22/0.99  sim_fw_subset_subsumed:                 0
% 2.22/0.99  sim_bw_subset_subsumed:                 0
% 2.22/0.99  sim_fw_subsumed:                        0
% 2.22/0.99  sim_bw_subsumed:                        0
% 2.22/0.99  sim_fw_subsumption_res:                 0
% 2.22/0.99  sim_bw_subsumption_res:                 0
% 2.22/0.99  sim_tautology_del:                      0
% 2.22/0.99  sim_eq_tautology_del:                   0
% 2.22/0.99  sim_eq_res_simp:                        0
% 2.22/0.99  sim_fw_demodulated:                     0
% 2.22/0.99  sim_bw_demodulated:                     0
% 2.22/0.99  sim_light_normalised:                   0
% 2.22/0.99  sim_joinable_taut:                      0
% 2.22/0.99  sim_joinable_simp:                      0
% 2.22/0.99  sim_ac_normalised:                      0
% 2.22/0.99  sim_smt_subsumption:                    0
% 2.22/0.99  
%------------------------------------------------------------------------------
