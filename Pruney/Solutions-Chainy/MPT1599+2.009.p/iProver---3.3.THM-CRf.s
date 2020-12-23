%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:20:09 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 497 expanded)
%              Number of clauses        :  102 ( 179 expanded)
%              Number of leaves         :   20 ( 120 expanded)
%              Depth                    :   25
%              Number of atoms          :  757 (2227 expanded)
%              Number of equality atoms :  147 ( 222 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   21 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v2_lattice3(k2_yellow_1(X0))
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
               => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

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

fof(f41,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
          & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
     => ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,sK3),k3_xboole_0(X1,sK3))
        & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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

fof(f39,plain,
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

fof(f42,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k3_xboole_0(sK2,sK3))
    & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
    & v2_lattice3(k2_yellow_1(sK1))
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f31,f41,f40,f39])).

fof(f65,plain,(
    v2_lattice3(k2_yellow_1(sK1)) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f15,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f58,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f57,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f38,plain,(
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

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f64,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f67,plain,(
    m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f66,plain,(
    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

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

fof(f25,plain,(
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
    inference(flattening,[],[f25])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f26])).

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
    inference(flattening,[],[f33])).

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
    inference(rectify,[],[f34])).

fof(f36,plain,(
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

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).

fof(f49,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f50,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

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

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f68,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k3_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
    inference(definition_unfolding,[],[f68,f44])).

cnf(c_22,negated_conjecture,
    ( v2_lattice3(k2_yellow_1(sK1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3,plain,
    ( ~ v2_lattice3(X0)
    | ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_15,plain,
    ( v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_368,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_15])).

cnf(c_369,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | v2_struct_0(k2_yellow_1(X0))
    | ~ l1_orders_2(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_368])).

cnf(c_13,plain,
    ( l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_373,plain,
    ( v2_struct_0(k2_yellow_1(X0))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r1_orders_2(k2_yellow_1(X0),X1,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_369,c_13])).

cnf(c_374,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | v2_struct_0(k2_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_373])).

cnf(c_407,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ v2_lattice3(X3)
    | ~ l1_orders_2(X3)
    | k2_yellow_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_374])).

cnf(c_408,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ v2_lattice3(k2_yellow_1(X0))
    | ~ l1_orders_2(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_412,plain,
    ( ~ v2_lattice3(k2_yellow_1(X0))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r1_orders_2(k2_yellow_1(X0),X1,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_408,c_13])).

cnf(c_413,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ v2_lattice3(k2_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_412])).

cnf(c_1084,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_22,c_413])).

cnf(c_18,plain,
    ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | r1_tarski(X1,X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_23,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_295,plain,
    ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | r1_tarski(X1,X2)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_23])).

cnf(c_296,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK1),X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
    | r1_tarski(X0,X1) ),
    inference(unflattening,[status(thm)],[c_295])).

cnf(c_1194,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X4,u1_struct_0(k2_yellow_1(sK1)))
    | r1_tarski(X3,X4)
    | X3 != X1
    | X4 != X2
    | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_1084,c_296])).

cnf(c_1195,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK1)))
    | r1_tarski(X1,X2)
    | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
    inference(unflattening,[status(thm)],[c_1194])).

cnf(c_2579,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(sK1),sK2,sK3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),X1)
    | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1195])).

cnf(c_8603,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
    | r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2)
    | k2_yellow_1(sK1) != k2_yellow_1(sK1) ),
    inference(instantiation,[status(thm)],[c_2579])).

cnf(c_1366,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_7664,plain,
    ( k11_lattice3(k2_yellow_1(sK1),sK2,sK3) = k11_lattice3(k2_yellow_1(sK1),sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1366])).

cnf(c_1372,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2571,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | X0 != k11_lattice3(k2_yellow_1(sK1),sK2,sK3)
    | X1 != u1_struct_0(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1372])).

cnf(c_7663,plain,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),X0)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | X0 != u1_struct_0(k2_yellow_1(sK1))
    | k11_lattice3(k2_yellow_1(sK1),sK2,sK3) != k11_lattice3(k2_yellow_1(sK1),sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2571])).

cnf(c_7666,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK1)
    | k11_lattice3(k2_yellow_1(sK1),sK2,sK3) != k11_lattice3(k2_yellow_1(sK1),sK2,sK3)
    | sK1 != u1_struct_0(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_7663])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1647,plain,
    ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_16,plain,
    ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1655,plain,
    ( m1_subset_1(sK3,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1647,c_16])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1646,plain,
    ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1652,plain,
    ( m1_subset_1(sK2,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1646,c_16])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,X0,X2) = k11_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_14,plain,
    ( v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_777,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k11_lattice3(X1,X0,X2) = k11_lattice3(X1,X2,X0)
    | k2_yellow_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_14])).

cnf(c_778,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | ~ v2_lattice3(k2_yellow_1(X1))
    | ~ l1_orders_2(k2_yellow_1(X1))
    | k11_lattice3(k2_yellow_1(X1),X2,X0) = k11_lattice3(k2_yellow_1(X1),X0,X2) ),
    inference(unflattening,[status(thm)],[c_777])).

cnf(c_792,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | ~ v2_lattice3(k2_yellow_1(X1))
    | k11_lattice3(k2_yellow_1(X1),X0,X2) = k11_lattice3(k2_yellow_1(X1),X2,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_778,c_13])).

cnf(c_1104,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | k11_lattice3(k2_yellow_1(X1),X0,X2) = k11_lattice3(k2_yellow_1(X1),X2,X0)
    | k2_yellow_1(X1) != k2_yellow_1(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_22,c_792])).

cnf(c_1637,plain,
    ( k11_lattice3(k2_yellow_1(X0),X1,X2) = k11_lattice3(k2_yellow_1(X0),X2,X1)
    | k2_yellow_1(X0) != k2_yellow_1(sK1)
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1104])).

cnf(c_1673,plain,
    ( k11_lattice3(k2_yellow_1(X0),X1,X2) = k11_lattice3(k2_yellow_1(X0),X2,X1)
    | k2_yellow_1(X0) != k2_yellow_1(sK1)
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1637,c_16])).

cnf(c_1987,plain,
    ( k11_lattice3(k2_yellow_1(sK1),X0,X1) = k11_lattice3(k2_yellow_1(sK1),X1,X0)
    | m1_subset_1(X0,sK1) != iProver_top
    | m1_subset_1(X1,sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1673])).

cnf(c_3285,plain,
    ( k11_lattice3(k2_yellow_1(sK1),sK2,X0) = k11_lattice3(k2_yellow_1(sK1),X0,sK2)
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1652,c_1987])).

cnf(c_3317,plain,
    ( k11_lattice3(k2_yellow_1(sK1),sK3,sK2) = k11_lattice3(k2_yellow_1(sK1),sK2,sK3) ),
    inference(superposition,[status(thm)],[c_1655,c_3285])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_862,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
    | k2_yellow_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_13])).

cnf(c_863,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),u1_struct_0(k2_yellow_1(X1))) ),
    inference(unflattening,[status(thm)],[c_862])).

cnf(c_11,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_138,plain,
    ( ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_3])).

cnf(c_139,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_138])).

cnf(c_754,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_139,c_14])).

cnf(c_755,plain,
    ( r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
    | ~ v2_lattice3(k2_yellow_1(X0))
    | ~ l1_orders_2(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_754])).

cnf(c_757,plain,
    ( ~ v2_lattice3(k2_yellow_1(X0))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_755,c_13])).

cnf(c_758,plain,
    ( r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
    | ~ v2_lattice3(k2_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_757])).

cnf(c_880,plain,
    ( r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ v2_lattice3(k2_yellow_1(X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_863,c_758])).

cnf(c_904,plain,
    ( r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_22,c_880])).

cnf(c_1643,plain,
    ( k2_yellow_1(X0) != k2_yellow_1(sK1)
    | r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X1) = iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_904])).

cnf(c_1682,plain,
    ( k2_yellow_1(X0) != k2_yellow_1(sK1)
    | r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X1) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1643,c_16])).

cnf(c_2032,plain,
    ( r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),X0,X1),X0) = iProver_top
    | m1_subset_1(X1,sK1) != iProver_top
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1682])).

cnf(c_3886,plain,
    ( r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3) = iProver_top
    | m1_subset_1(sK3,sK1) != iProver_top
    | m1_subset_1(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3317,c_2032])).

cnf(c_26,plain,
    ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_27,plain,
    ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1375,plain,
    ( X0 != X1
    | k2_yellow_1(X0) = k2_yellow_1(X1) ),
    theory(equality)).

cnf(c_1383,plain,
    ( k2_yellow_1(sK1) = k2_yellow_1(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1375])).

cnf(c_1385,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1366])).

cnf(c_10,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_145,plain,
    ( ~ v2_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_3])).

cnf(c_146,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_145])).

cnf(c_727,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_146,c_14])).

cnf(c_728,plain,
    ( r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
    | ~ v2_lattice3(k2_yellow_1(X0))
    | ~ l1_orders_2(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_727])).

cnf(c_732,plain,
    ( ~ v2_lattice3(k2_yellow_1(X0))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_728,c_13])).

cnf(c_733,plain,
    ( r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
    | ~ v2_lattice3(k2_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_732])).

cnf(c_881,plain,
    ( r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ v2_lattice3(k2_yellow_1(X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_863,c_733])).

cnf(c_887,plain,
    ( r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_22,c_881])).

cnf(c_1866,plain,
    ( r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),X0,sK3),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    | k2_yellow_1(sK1) != k2_yellow_1(sK1) ),
    inference(instantiation,[status(thm)],[c_887])).

cnf(c_2018,plain,
    ( r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
    | k2_yellow_1(sK1) != k2_yellow_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1866])).

cnf(c_2019,plain,
    ( k2_yellow_1(sK1) != k2_yellow_1(sK1)
    | r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2018])).

cnf(c_5740,plain,
    ( r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3886,c_26,c_27,c_1383,c_1385,c_2019])).

cnf(c_1636,plain,
    ( k2_yellow_1(X0) != k2_yellow_1(sK1)
    | r1_orders_2(k2_yellow_1(X0),X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
    | r1_tarski(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1195])).

cnf(c_1716,plain,
    ( k2_yellow_1(X0) != k2_yellow_1(sK1)
    | r1_orders_2(k2_yellow_1(X0),X1,X2) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
    | r1_tarski(X1,X2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1636,c_16])).

cnf(c_1717,plain,
    ( k2_yellow_1(X0) != k2_yellow_1(sK1)
    | r1_orders_2(k2_yellow_1(X0),X1,X2) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,sK1) != iProver_top
    | m1_subset_1(X2,sK1) != iProver_top
    | r1_tarski(X1,X2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1716,c_16])).

cnf(c_2792,plain,
    ( r1_orders_2(k2_yellow_1(sK1),X0,X1) != iProver_top
    | m1_subset_1(X1,sK1) != iProver_top
    | m1_subset_1(X0,sK1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1717])).

cnf(c_5745,plain,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK1) != iProver_top
    | m1_subset_1(sK3,sK1) != iProver_top
    | r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5740,c_2792])).

cnf(c_5746,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK1)
    | ~ m1_subset_1(sK3,sK1)
    | r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5745])).

cnf(c_1367,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2185,plain,
    ( X0 != X1
    | X0 = u1_struct_0(k2_yellow_1(sK1))
    | u1_struct_0(k2_yellow_1(sK1)) != X1 ),
    inference(instantiation,[status(thm)],[c_1367])).

cnf(c_2186,plain,
    ( u1_struct_0(k2_yellow_1(sK1)) != sK1
    | sK1 = u1_struct_0(k2_yellow_1(sK1))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2185])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1649,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1648,plain,
    ( r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2138,plain,
    ( r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3) != iProver_top
    | r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1649,c_1648])).

cnf(c_2139,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3)
    | ~ r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2138])).

cnf(c_1876,plain,
    ( r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),X0,sK3),X0)
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    | k2_yellow_1(sK1) != k2_yellow_1(sK1) ),
    inference(instantiation,[status(thm)],[c_904])).

cnf(c_2056,plain,
    ( r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
    | k2_yellow_1(sK1) != k2_yellow_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1876])).

cnf(c_1975,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,X0),u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(instantiation,[status(thm)],[c_863])).

cnf(c_2049,plain,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(instantiation,[status(thm)],[c_1975])).

cnf(c_1830,plain,
    ( m1_subset_1(sK3,sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1655])).

cnf(c_35,plain,
    ( u1_struct_0(k2_yellow_1(sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8603,c_7664,c_7666,c_5746,c_2186,c_2139,c_2056,c_2049,c_1830,c_1385,c_1383,c_35,c_20,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:19:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.37/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.00  
% 2.37/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.37/1.00  
% 2.37/1.00  ------  iProver source info
% 2.37/1.00  
% 2.37/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.37/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.37/1.00  git: non_committed_changes: false
% 2.37/1.00  git: last_make_outside_of_git: false
% 2.37/1.00  
% 2.37/1.00  ------ 
% 2.37/1.00  
% 2.37/1.00  ------ Input Options
% 2.37/1.00  
% 2.37/1.00  --out_options                           all
% 2.37/1.00  --tptp_safe_out                         true
% 2.37/1.00  --problem_path                          ""
% 2.37/1.00  --include_path                          ""
% 2.37/1.00  --clausifier                            res/vclausify_rel
% 2.37/1.00  --clausifier_options                    --mode clausify
% 2.37/1.00  --stdin                                 false
% 2.37/1.00  --stats_out                             all
% 2.37/1.00  
% 2.37/1.00  ------ General Options
% 2.37/1.00  
% 2.37/1.00  --fof                                   false
% 2.37/1.00  --time_out_real                         305.
% 2.37/1.00  --time_out_virtual                      -1.
% 2.37/1.00  --symbol_type_check                     false
% 2.37/1.00  --clausify_out                          false
% 2.37/1.00  --sig_cnt_out                           false
% 2.37/1.00  --trig_cnt_out                          false
% 2.37/1.00  --trig_cnt_out_tolerance                1.
% 2.37/1.00  --trig_cnt_out_sk_spl                   false
% 2.37/1.00  --abstr_cl_out                          false
% 2.37/1.00  
% 2.37/1.00  ------ Global Options
% 2.37/1.00  
% 2.37/1.00  --schedule                              default
% 2.37/1.00  --add_important_lit                     false
% 2.37/1.00  --prop_solver_per_cl                    1000
% 2.37/1.00  --min_unsat_core                        false
% 2.37/1.00  --soft_assumptions                      false
% 2.37/1.00  --soft_lemma_size                       3
% 2.37/1.00  --prop_impl_unit_size                   0
% 2.37/1.00  --prop_impl_unit                        []
% 2.37/1.00  --share_sel_clauses                     true
% 2.37/1.00  --reset_solvers                         false
% 2.37/1.00  --bc_imp_inh                            [conj_cone]
% 2.37/1.00  --conj_cone_tolerance                   3.
% 2.37/1.00  --extra_neg_conj                        none
% 2.37/1.00  --large_theory_mode                     true
% 2.37/1.00  --prolific_symb_bound                   200
% 2.37/1.00  --lt_threshold                          2000
% 2.37/1.00  --clause_weak_htbl                      true
% 2.37/1.00  --gc_record_bc_elim                     false
% 2.37/1.00  
% 2.37/1.00  ------ Preprocessing Options
% 2.37/1.00  
% 2.37/1.00  --preprocessing_flag                    true
% 2.37/1.00  --time_out_prep_mult                    0.1
% 2.37/1.00  --splitting_mode                        input
% 2.37/1.00  --splitting_grd                         true
% 2.37/1.00  --splitting_cvd                         false
% 2.37/1.00  --splitting_cvd_svl                     false
% 2.37/1.00  --splitting_nvd                         32
% 2.37/1.00  --sub_typing                            true
% 2.37/1.00  --prep_gs_sim                           true
% 2.37/1.00  --prep_unflatten                        true
% 2.37/1.00  --prep_res_sim                          true
% 2.37/1.00  --prep_upred                            true
% 2.37/1.00  --prep_sem_filter                       exhaustive
% 2.37/1.00  --prep_sem_filter_out                   false
% 2.37/1.00  --pred_elim                             true
% 2.37/1.00  --res_sim_input                         true
% 2.37/1.00  --eq_ax_congr_red                       true
% 2.37/1.00  --pure_diseq_elim                       true
% 2.37/1.00  --brand_transform                       false
% 2.37/1.00  --non_eq_to_eq                          false
% 2.37/1.00  --prep_def_merge                        true
% 2.37/1.00  --prep_def_merge_prop_impl              false
% 2.37/1.00  --prep_def_merge_mbd                    true
% 2.37/1.00  --prep_def_merge_tr_red                 false
% 2.37/1.00  --prep_def_merge_tr_cl                  false
% 2.37/1.00  --smt_preprocessing                     true
% 2.37/1.00  --smt_ac_axioms                         fast
% 2.37/1.00  --preprocessed_out                      false
% 2.37/1.00  --preprocessed_stats                    false
% 2.37/1.00  
% 2.37/1.00  ------ Abstraction refinement Options
% 2.37/1.00  
% 2.37/1.00  --abstr_ref                             []
% 2.37/1.00  --abstr_ref_prep                        false
% 2.37/1.00  --abstr_ref_until_sat                   false
% 2.37/1.00  --abstr_ref_sig_restrict                funpre
% 2.37/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.37/1.00  --abstr_ref_under                       []
% 2.37/1.00  
% 2.37/1.00  ------ SAT Options
% 2.37/1.00  
% 2.37/1.00  --sat_mode                              false
% 2.37/1.00  --sat_fm_restart_options                ""
% 2.37/1.00  --sat_gr_def                            false
% 2.37/1.00  --sat_epr_types                         true
% 2.37/1.00  --sat_non_cyclic_types                  false
% 2.37/1.00  --sat_finite_models                     false
% 2.37/1.00  --sat_fm_lemmas                         false
% 2.37/1.00  --sat_fm_prep                           false
% 2.37/1.00  --sat_fm_uc_incr                        true
% 2.37/1.00  --sat_out_model                         small
% 2.37/1.00  --sat_out_clauses                       false
% 2.37/1.00  
% 2.37/1.00  ------ QBF Options
% 2.37/1.00  
% 2.37/1.00  --qbf_mode                              false
% 2.37/1.00  --qbf_elim_univ                         false
% 2.37/1.00  --qbf_dom_inst                          none
% 2.37/1.00  --qbf_dom_pre_inst                      false
% 2.37/1.00  --qbf_sk_in                             false
% 2.37/1.00  --qbf_pred_elim                         true
% 2.37/1.00  --qbf_split                             512
% 2.37/1.00  
% 2.37/1.00  ------ BMC1 Options
% 2.37/1.00  
% 2.37/1.00  --bmc1_incremental                      false
% 2.37/1.00  --bmc1_axioms                           reachable_all
% 2.37/1.00  --bmc1_min_bound                        0
% 2.37/1.00  --bmc1_max_bound                        -1
% 2.37/1.00  --bmc1_max_bound_default                -1
% 2.37/1.00  --bmc1_symbol_reachability              true
% 2.37/1.00  --bmc1_property_lemmas                  false
% 2.37/1.00  --bmc1_k_induction                      false
% 2.37/1.00  --bmc1_non_equiv_states                 false
% 2.37/1.00  --bmc1_deadlock                         false
% 2.37/1.00  --bmc1_ucm                              false
% 2.37/1.00  --bmc1_add_unsat_core                   none
% 2.37/1.00  --bmc1_unsat_core_children              false
% 2.37/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.37/1.00  --bmc1_out_stat                         full
% 2.37/1.00  --bmc1_ground_init                      false
% 2.37/1.00  --bmc1_pre_inst_next_state              false
% 2.37/1.00  --bmc1_pre_inst_state                   false
% 2.37/1.00  --bmc1_pre_inst_reach_state             false
% 2.37/1.00  --bmc1_out_unsat_core                   false
% 2.37/1.00  --bmc1_aig_witness_out                  false
% 2.37/1.00  --bmc1_verbose                          false
% 2.37/1.00  --bmc1_dump_clauses_tptp                false
% 2.37/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.37/1.00  --bmc1_dump_file                        -
% 2.37/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.37/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.37/1.00  --bmc1_ucm_extend_mode                  1
% 2.37/1.00  --bmc1_ucm_init_mode                    2
% 2.37/1.00  --bmc1_ucm_cone_mode                    none
% 2.37/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.37/1.00  --bmc1_ucm_relax_model                  4
% 2.37/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.37/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.37/1.00  --bmc1_ucm_layered_model                none
% 2.37/1.00  --bmc1_ucm_max_lemma_size               10
% 2.37/1.00  
% 2.37/1.00  ------ AIG Options
% 2.37/1.00  
% 2.37/1.00  --aig_mode                              false
% 2.37/1.00  
% 2.37/1.00  ------ Instantiation Options
% 2.37/1.00  
% 2.37/1.00  --instantiation_flag                    true
% 2.37/1.00  --inst_sos_flag                         false
% 2.37/1.00  --inst_sos_phase                        true
% 2.37/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.37/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.37/1.00  --inst_lit_sel_side                     num_symb
% 2.37/1.00  --inst_solver_per_active                1400
% 2.37/1.00  --inst_solver_calls_frac                1.
% 2.37/1.00  --inst_passive_queue_type               priority_queues
% 2.37/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.37/1.00  --inst_passive_queues_freq              [25;2]
% 2.37/1.00  --inst_dismatching                      true
% 2.37/1.00  --inst_eager_unprocessed_to_passive     true
% 2.37/1.00  --inst_prop_sim_given                   true
% 2.37/1.00  --inst_prop_sim_new                     false
% 2.37/1.00  --inst_subs_new                         false
% 2.37/1.00  --inst_eq_res_simp                      false
% 2.37/1.00  --inst_subs_given                       false
% 2.37/1.00  --inst_orphan_elimination               true
% 2.37/1.00  --inst_learning_loop_flag               true
% 2.37/1.00  --inst_learning_start                   3000
% 2.37/1.00  --inst_learning_factor                  2
% 2.37/1.00  --inst_start_prop_sim_after_learn       3
% 2.37/1.00  --inst_sel_renew                        solver
% 2.37/1.00  --inst_lit_activity_flag                true
% 2.37/1.00  --inst_restr_to_given                   false
% 2.37/1.00  --inst_activity_threshold               500
% 2.37/1.00  --inst_out_proof                        true
% 2.37/1.00  
% 2.37/1.00  ------ Resolution Options
% 2.37/1.00  
% 2.37/1.00  --resolution_flag                       true
% 2.37/1.00  --res_lit_sel                           adaptive
% 2.37/1.00  --res_lit_sel_side                      none
% 2.37/1.00  --res_ordering                          kbo
% 2.37/1.00  --res_to_prop_solver                    active
% 2.37/1.00  --res_prop_simpl_new                    false
% 2.37/1.00  --res_prop_simpl_given                  true
% 2.37/1.00  --res_passive_queue_type                priority_queues
% 2.37/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.37/1.00  --res_passive_queues_freq               [15;5]
% 2.37/1.00  --res_forward_subs                      full
% 2.37/1.00  --res_backward_subs                     full
% 2.37/1.00  --res_forward_subs_resolution           true
% 2.37/1.00  --res_backward_subs_resolution          true
% 2.37/1.00  --res_orphan_elimination                true
% 2.37/1.00  --res_time_limit                        2.
% 2.37/1.00  --res_out_proof                         true
% 2.37/1.00  
% 2.37/1.00  ------ Superposition Options
% 2.37/1.00  
% 2.37/1.00  --superposition_flag                    true
% 2.37/1.00  --sup_passive_queue_type                priority_queues
% 2.37/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.37/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.37/1.00  --demod_completeness_check              fast
% 2.37/1.00  --demod_use_ground                      true
% 2.37/1.00  --sup_to_prop_solver                    passive
% 2.37/1.00  --sup_prop_simpl_new                    true
% 2.37/1.00  --sup_prop_simpl_given                  true
% 2.37/1.00  --sup_fun_splitting                     false
% 2.37/1.00  --sup_smt_interval                      50000
% 2.37/1.00  
% 2.37/1.00  ------ Superposition Simplification Setup
% 2.37/1.00  
% 2.37/1.00  --sup_indices_passive                   []
% 2.37/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.37/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.37/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.37/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.37/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.37/1.00  --sup_full_bw                           [BwDemod]
% 2.37/1.00  --sup_immed_triv                        [TrivRules]
% 2.37/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.37/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.37/1.00  --sup_immed_bw_main                     []
% 2.37/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.37/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.37/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.37/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.37/1.00  
% 2.37/1.00  ------ Combination Options
% 2.37/1.00  
% 2.37/1.00  --comb_res_mult                         3
% 2.37/1.00  --comb_sup_mult                         2
% 2.37/1.00  --comb_inst_mult                        10
% 2.37/1.00  
% 2.37/1.00  ------ Debug Options
% 2.37/1.00  
% 2.37/1.00  --dbg_backtrace                         false
% 2.37/1.00  --dbg_dump_prop_clauses                 false
% 2.37/1.00  --dbg_dump_prop_clauses_file            -
% 2.37/1.00  --dbg_out_stat                          false
% 2.37/1.00  ------ Parsing...
% 2.37/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.37/1.00  
% 2.37/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.37/1.00  
% 2.37/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.37/1.00  
% 2.37/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.37/1.00  ------ Proving...
% 2.37/1.00  ------ Problem Properties 
% 2.37/1.00  
% 2.37/1.00  
% 2.37/1.00  clauses                                 16
% 2.37/1.00  conjectures                             3
% 2.51/1.00  EPR                                     0
% 2.51/1.00  Horn                                    13
% 2.51/1.00  unary                                   4
% 2.51/1.00  binary                                  0
% 2.51/1.00  lits                                    75
% 2.51/1.00  lits eq                                 16
% 2.51/1.00  fd_pure                                 0
% 2.51/1.00  fd_pseudo                               0
% 2.51/1.00  fd_cond                                 0
% 2.51/1.00  fd_pseudo_cond                          4
% 2.51/1.00  AC symbols                              0
% 2.51/1.00  
% 2.51/1.00  ------ Schedule dynamic 5 is on 
% 2.51/1.00  
% 2.51/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.51/1.00  
% 2.51/1.00  
% 2.51/1.00  ------ 
% 2.51/1.00  Current options:
% 2.51/1.00  ------ 
% 2.51/1.00  
% 2.51/1.00  ------ Input Options
% 2.51/1.00  
% 2.51/1.00  --out_options                           all
% 2.51/1.00  --tptp_safe_out                         true
% 2.51/1.00  --problem_path                          ""
% 2.51/1.00  --include_path                          ""
% 2.51/1.00  --clausifier                            res/vclausify_rel
% 2.51/1.00  --clausifier_options                    --mode clausify
% 2.51/1.00  --stdin                                 false
% 2.51/1.00  --stats_out                             all
% 2.51/1.00  
% 2.51/1.00  ------ General Options
% 2.51/1.00  
% 2.51/1.00  --fof                                   false
% 2.51/1.00  --time_out_real                         305.
% 2.51/1.00  --time_out_virtual                      -1.
% 2.51/1.00  --symbol_type_check                     false
% 2.51/1.00  --clausify_out                          false
% 2.51/1.00  --sig_cnt_out                           false
% 2.51/1.00  --trig_cnt_out                          false
% 2.51/1.00  --trig_cnt_out_tolerance                1.
% 2.51/1.00  --trig_cnt_out_sk_spl                   false
% 2.51/1.00  --abstr_cl_out                          false
% 2.51/1.00  
% 2.51/1.00  ------ Global Options
% 2.51/1.00  
% 2.51/1.00  --schedule                              default
% 2.51/1.00  --add_important_lit                     false
% 2.51/1.00  --prop_solver_per_cl                    1000
% 2.51/1.00  --min_unsat_core                        false
% 2.51/1.00  --soft_assumptions                      false
% 2.51/1.00  --soft_lemma_size                       3
% 2.51/1.00  --prop_impl_unit_size                   0
% 2.51/1.00  --prop_impl_unit                        []
% 2.51/1.00  --share_sel_clauses                     true
% 2.51/1.00  --reset_solvers                         false
% 2.51/1.00  --bc_imp_inh                            [conj_cone]
% 2.51/1.00  --conj_cone_tolerance                   3.
% 2.51/1.00  --extra_neg_conj                        none
% 2.51/1.00  --large_theory_mode                     true
% 2.51/1.00  --prolific_symb_bound                   200
% 2.51/1.00  --lt_threshold                          2000
% 2.51/1.00  --clause_weak_htbl                      true
% 2.51/1.00  --gc_record_bc_elim                     false
% 2.51/1.00  
% 2.51/1.00  ------ Preprocessing Options
% 2.51/1.00  
% 2.51/1.00  --preprocessing_flag                    true
% 2.51/1.00  --time_out_prep_mult                    0.1
% 2.51/1.00  --splitting_mode                        input
% 2.51/1.00  --splitting_grd                         true
% 2.51/1.00  --splitting_cvd                         false
% 2.51/1.00  --splitting_cvd_svl                     false
% 2.51/1.00  --splitting_nvd                         32
% 2.51/1.00  --sub_typing                            true
% 2.51/1.00  --prep_gs_sim                           true
% 2.51/1.00  --prep_unflatten                        true
% 2.51/1.00  --prep_res_sim                          true
% 2.51/1.00  --prep_upred                            true
% 2.51/1.00  --prep_sem_filter                       exhaustive
% 2.51/1.00  --prep_sem_filter_out                   false
% 2.51/1.00  --pred_elim                             true
% 2.51/1.00  --res_sim_input                         true
% 2.51/1.00  --eq_ax_congr_red                       true
% 2.51/1.00  --pure_diseq_elim                       true
% 2.51/1.00  --brand_transform                       false
% 2.51/1.00  --non_eq_to_eq                          false
% 2.51/1.00  --prep_def_merge                        true
% 2.51/1.00  --prep_def_merge_prop_impl              false
% 2.51/1.00  --prep_def_merge_mbd                    true
% 2.51/1.00  --prep_def_merge_tr_red                 false
% 2.51/1.00  --prep_def_merge_tr_cl                  false
% 2.51/1.00  --smt_preprocessing                     true
% 2.51/1.00  --smt_ac_axioms                         fast
% 2.51/1.00  --preprocessed_out                      false
% 2.51/1.00  --preprocessed_stats                    false
% 2.51/1.00  
% 2.51/1.00  ------ Abstraction refinement Options
% 2.51/1.00  
% 2.51/1.00  --abstr_ref                             []
% 2.51/1.00  --abstr_ref_prep                        false
% 2.51/1.00  --abstr_ref_until_sat                   false
% 2.51/1.00  --abstr_ref_sig_restrict                funpre
% 2.51/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.51/1.00  --abstr_ref_under                       []
% 2.51/1.00  
% 2.51/1.00  ------ SAT Options
% 2.51/1.00  
% 2.51/1.00  --sat_mode                              false
% 2.51/1.00  --sat_fm_restart_options                ""
% 2.51/1.00  --sat_gr_def                            false
% 2.51/1.00  --sat_epr_types                         true
% 2.51/1.00  --sat_non_cyclic_types                  false
% 2.51/1.00  --sat_finite_models                     false
% 2.51/1.00  --sat_fm_lemmas                         false
% 2.51/1.00  --sat_fm_prep                           false
% 2.51/1.00  --sat_fm_uc_incr                        true
% 2.51/1.00  --sat_out_model                         small
% 2.51/1.00  --sat_out_clauses                       false
% 2.51/1.00  
% 2.51/1.00  ------ QBF Options
% 2.51/1.00  
% 2.51/1.00  --qbf_mode                              false
% 2.51/1.00  --qbf_elim_univ                         false
% 2.51/1.00  --qbf_dom_inst                          none
% 2.51/1.00  --qbf_dom_pre_inst                      false
% 2.51/1.00  --qbf_sk_in                             false
% 2.51/1.00  --qbf_pred_elim                         true
% 2.51/1.00  --qbf_split                             512
% 2.51/1.00  
% 2.51/1.00  ------ BMC1 Options
% 2.51/1.00  
% 2.51/1.00  --bmc1_incremental                      false
% 2.51/1.00  --bmc1_axioms                           reachable_all
% 2.51/1.00  --bmc1_min_bound                        0
% 2.51/1.00  --bmc1_max_bound                        -1
% 2.51/1.00  --bmc1_max_bound_default                -1
% 2.51/1.00  --bmc1_symbol_reachability              true
% 2.51/1.00  --bmc1_property_lemmas                  false
% 2.51/1.00  --bmc1_k_induction                      false
% 2.51/1.00  --bmc1_non_equiv_states                 false
% 2.51/1.00  --bmc1_deadlock                         false
% 2.51/1.00  --bmc1_ucm                              false
% 2.51/1.00  --bmc1_add_unsat_core                   none
% 2.51/1.00  --bmc1_unsat_core_children              false
% 2.51/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.51/1.00  --bmc1_out_stat                         full
% 2.51/1.00  --bmc1_ground_init                      false
% 2.51/1.00  --bmc1_pre_inst_next_state              false
% 2.51/1.00  --bmc1_pre_inst_state                   false
% 2.51/1.00  --bmc1_pre_inst_reach_state             false
% 2.51/1.00  --bmc1_out_unsat_core                   false
% 2.51/1.00  --bmc1_aig_witness_out                  false
% 2.51/1.00  --bmc1_verbose                          false
% 2.51/1.00  --bmc1_dump_clauses_tptp                false
% 2.51/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.51/1.00  --bmc1_dump_file                        -
% 2.51/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.51/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.51/1.00  --bmc1_ucm_extend_mode                  1
% 2.51/1.00  --bmc1_ucm_init_mode                    2
% 2.51/1.00  --bmc1_ucm_cone_mode                    none
% 2.51/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.51/1.00  --bmc1_ucm_relax_model                  4
% 2.51/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.51/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.51/1.00  --bmc1_ucm_layered_model                none
% 2.51/1.00  --bmc1_ucm_max_lemma_size               10
% 2.51/1.00  
% 2.51/1.00  ------ AIG Options
% 2.51/1.00  
% 2.51/1.00  --aig_mode                              false
% 2.51/1.00  
% 2.51/1.00  ------ Instantiation Options
% 2.51/1.00  
% 2.51/1.00  --instantiation_flag                    true
% 2.51/1.00  --inst_sos_flag                         false
% 2.51/1.00  --inst_sos_phase                        true
% 2.51/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.51/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.51/1.00  --inst_lit_sel_side                     none
% 2.51/1.00  --inst_solver_per_active                1400
% 2.51/1.00  --inst_solver_calls_frac                1.
% 2.51/1.00  --inst_passive_queue_type               priority_queues
% 2.51/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.51/1.00  --inst_passive_queues_freq              [25;2]
% 2.51/1.00  --inst_dismatching                      true
% 2.51/1.00  --inst_eager_unprocessed_to_passive     true
% 2.51/1.00  --inst_prop_sim_given                   true
% 2.51/1.00  --inst_prop_sim_new                     false
% 2.51/1.00  --inst_subs_new                         false
% 2.51/1.00  --inst_eq_res_simp                      false
% 2.51/1.00  --inst_subs_given                       false
% 2.51/1.00  --inst_orphan_elimination               true
% 2.51/1.00  --inst_learning_loop_flag               true
% 2.51/1.00  --inst_learning_start                   3000
% 2.51/1.00  --inst_learning_factor                  2
% 2.51/1.00  --inst_start_prop_sim_after_learn       3
% 2.51/1.00  --inst_sel_renew                        solver
% 2.51/1.00  --inst_lit_activity_flag                true
% 2.51/1.00  --inst_restr_to_given                   false
% 2.51/1.00  --inst_activity_threshold               500
% 2.51/1.00  --inst_out_proof                        true
% 2.51/1.00  
% 2.51/1.00  ------ Resolution Options
% 2.51/1.00  
% 2.51/1.00  --resolution_flag                       false
% 2.51/1.00  --res_lit_sel                           adaptive
% 2.51/1.00  --res_lit_sel_side                      none
% 2.51/1.00  --res_ordering                          kbo
% 2.51/1.00  --res_to_prop_solver                    active
% 2.51/1.00  --res_prop_simpl_new                    false
% 2.51/1.00  --res_prop_simpl_given                  true
% 2.51/1.00  --res_passive_queue_type                priority_queues
% 2.51/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.51/1.00  --res_passive_queues_freq               [15;5]
% 2.51/1.00  --res_forward_subs                      full
% 2.51/1.00  --res_backward_subs                     full
% 2.51/1.00  --res_forward_subs_resolution           true
% 2.51/1.00  --res_backward_subs_resolution          true
% 2.51/1.00  --res_orphan_elimination                true
% 2.51/1.00  --res_time_limit                        2.
% 2.51/1.00  --res_out_proof                         true
% 2.51/1.00  
% 2.51/1.00  ------ Superposition Options
% 2.51/1.00  
% 2.51/1.00  --superposition_flag                    true
% 2.51/1.00  --sup_passive_queue_type                priority_queues
% 2.51/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.51/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.51/1.00  --demod_completeness_check              fast
% 2.51/1.00  --demod_use_ground                      true
% 2.51/1.00  --sup_to_prop_solver                    passive
% 2.51/1.00  --sup_prop_simpl_new                    true
% 2.51/1.00  --sup_prop_simpl_given                  true
% 2.51/1.00  --sup_fun_splitting                     false
% 2.51/1.00  --sup_smt_interval                      50000
% 2.51/1.00  
% 2.51/1.00  ------ Superposition Simplification Setup
% 2.51/1.00  
% 2.51/1.00  --sup_indices_passive                   []
% 2.51/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.51/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.51/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.51/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.51/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.51/1.00  --sup_full_bw                           [BwDemod]
% 2.51/1.00  --sup_immed_triv                        [TrivRules]
% 2.51/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.51/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.51/1.00  --sup_immed_bw_main                     []
% 2.51/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.51/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.51/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.51/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.51/1.00  
% 2.51/1.00  ------ Combination Options
% 2.51/1.00  
% 2.51/1.00  --comb_res_mult                         3
% 2.51/1.00  --comb_sup_mult                         2
% 2.51/1.00  --comb_inst_mult                        10
% 2.51/1.00  
% 2.51/1.00  ------ Debug Options
% 2.51/1.00  
% 2.51/1.00  --dbg_backtrace                         false
% 2.51/1.00  --dbg_dump_prop_clauses                 false
% 2.51/1.00  --dbg_dump_prop_clauses_file            -
% 2.51/1.00  --dbg_out_stat                          false
% 2.51/1.00  
% 2.51/1.00  
% 2.51/1.00  
% 2.51/1.00  
% 2.51/1.00  ------ Proving...
% 2.51/1.00  
% 2.51/1.00  
% 2.51/1.00  % SZS status Theorem for theBenchmark.p
% 2.51/1.00  
% 2.51/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.51/1.00  
% 2.51/1.00  fof(f12,conjecture,(
% 2.51/1.00    ! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 2.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/1.00  
% 2.51/1.00  fof(f13,negated_conjecture,(
% 2.51/1.00    ~! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 2.51/1.00    inference(negated_conjecture,[],[f12])).
% 2.51/1.00  
% 2.51/1.00  fof(f30,plain,(
% 2.51/1.00    ? [X0] : ((? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0))) & ~v1_xboole_0(X0))),
% 2.51/1.00    inference(ennf_transformation,[],[f13])).
% 2.51/1.00  
% 2.51/1.00  fof(f31,plain,(
% 2.51/1.00    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0))),
% 2.51/1.00    inference(flattening,[],[f30])).
% 2.51/1.00  
% 2.51/1.00  fof(f41,plain,(
% 2.51/1.00    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) => (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,sK3),k3_xboole_0(X1,sK3)) & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0))))) )),
% 2.51/1.00    introduced(choice_axiom,[])).
% 2.51/1.00  
% 2.51/1.00  fof(f40,plain,(
% 2.51/1.00    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) => (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),sK2,X2),k3_xboole_0(sK2,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(X0))))) )),
% 2.51/1.00    introduced(choice_axiom,[])).
% 2.51/1.00  
% 2.51/1.00  fof(f39,plain,(
% 2.51/1.00    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK1),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK1)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))) & v2_lattice3(k2_yellow_1(sK1)) & ~v1_xboole_0(sK1))),
% 2.51/1.00    introduced(choice_axiom,[])).
% 2.51/1.00  
% 2.51/1.00  fof(f42,plain,(
% 2.51/1.00    ((~r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k3_xboole_0(sK2,sK3)) & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))) & v2_lattice3(k2_yellow_1(sK1)) & ~v1_xboole_0(sK1)),
% 2.51/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f31,f41,f40,f39])).
% 2.51/1.00  
% 2.51/1.00  fof(f65,plain,(
% 2.51/1.00    v2_lattice3(k2_yellow_1(sK1))),
% 2.51/1.00    inference(cnf_transformation,[],[f42])).
% 2.51/1.00  
% 2.51/1.00  fof(f4,axiom,(
% 2.51/1.00    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 2.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/1.00  
% 2.51/1.00  fof(f21,plain,(
% 2.51/1.00    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 2.51/1.00    inference(ennf_transformation,[],[f4])).
% 2.51/1.00  
% 2.51/1.00  fof(f22,plain,(
% 2.51/1.00    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 2.51/1.00    inference(flattening,[],[f21])).
% 2.51/1.00  
% 2.51/1.00  fof(f47,plain,(
% 2.51/1.00    ( ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0)) )),
% 2.51/1.00    inference(cnf_transformation,[],[f22])).
% 2.51/1.00  
% 2.51/1.00  fof(f3,axiom,(
% 2.51/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 2.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/1.00  
% 2.51/1.00  fof(f19,plain,(
% 2.51/1.00    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.51/1.00    inference(ennf_transformation,[],[f3])).
% 2.51/1.00  
% 2.51/1.00  fof(f20,plain,(
% 2.51/1.00    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.51/1.00    inference(flattening,[],[f19])).
% 2.51/1.00  
% 2.51/1.00  fof(f32,plain,(
% 2.51/1.00    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.51/1.00    inference(nnf_transformation,[],[f20])).
% 2.51/1.00  
% 2.51/1.00  fof(f46,plain,(
% 2.51/1.00    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.51/1.00    inference(cnf_transformation,[],[f32])).
% 2.51/1.00  
% 2.51/1.00  fof(f9,axiom,(
% 2.51/1.00    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 2.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/1.00  
% 2.51/1.00  fof(f14,plain,(
% 2.51/1.00    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 2.51/1.00    inference(pure_predicate_removal,[],[f9])).
% 2.51/1.00  
% 2.51/1.00  fof(f15,plain,(
% 2.51/1.00    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 2.51/1.00    inference(pure_predicate_removal,[],[f14])).
% 2.51/1.00  
% 2.51/1.00  fof(f58,plain,(
% 2.51/1.00    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 2.51/1.00    inference(cnf_transformation,[],[f15])).
% 2.51/1.00  
% 2.51/1.00  fof(f8,axiom,(
% 2.51/1.00    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 2.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/1.00  
% 2.51/1.00  fof(f16,plain,(
% 2.51/1.00    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 2.51/1.00    inference(pure_predicate_removal,[],[f8])).
% 2.51/1.00  
% 2.51/1.00  fof(f57,plain,(
% 2.51/1.00    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 2.51/1.00    inference(cnf_transformation,[],[f16])).
% 2.51/1.00  
% 2.51/1.00  fof(f11,axiom,(
% 2.51/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 2.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/1.00  
% 2.51/1.00  fof(f29,plain,(
% 2.51/1.00    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 2.51/1.00    inference(ennf_transformation,[],[f11])).
% 2.51/1.00  
% 2.51/1.00  fof(f38,plain,(
% 2.51/1.00    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 2.51/1.00    inference(nnf_transformation,[],[f29])).
% 2.51/1.00  
% 2.51/1.00  fof(f62,plain,(
% 2.51/1.00    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 2.51/1.00    inference(cnf_transformation,[],[f38])).
% 2.51/1.00  
% 2.51/1.00  fof(f64,plain,(
% 2.51/1.00    ~v1_xboole_0(sK1)),
% 2.51/1.00    inference(cnf_transformation,[],[f42])).
% 2.51/1.00  
% 2.51/1.00  fof(f67,plain,(
% 2.51/1.00    m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))),
% 2.51/1.00    inference(cnf_transformation,[],[f42])).
% 2.51/1.00  
% 2.51/1.00  fof(f10,axiom,(
% 2.51/1.00    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 2.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/1.00  
% 2.51/1.00  fof(f60,plain,(
% 2.51/1.00    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 2.51/1.00    inference(cnf_transformation,[],[f10])).
% 2.51/1.00  
% 2.51/1.00  fof(f66,plain,(
% 2.51/1.00    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))),
% 2.51/1.00    inference(cnf_transformation,[],[f42])).
% 2.51/1.00  
% 2.51/1.00  fof(f7,axiom,(
% 2.51/1.00    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1))))),
% 2.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/1.00  
% 2.51/1.00  fof(f27,plain,(
% 2.51/1.00    ! [X0] : (! [X1] : (! [X2] : (k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 2.51/1.00    inference(ennf_transformation,[],[f7])).
% 2.51/1.00  
% 2.51/1.00  fof(f28,plain,(
% 2.51/1.00    ! [X0] : (! [X1] : (! [X2] : (k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 2.51/1.00    inference(flattening,[],[f27])).
% 2.51/1.00  
% 2.51/1.00  fof(f56,plain,(
% 2.51/1.00    ( ! [X2,X0,X1] : (k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 2.51/1.00    inference(cnf_transformation,[],[f28])).
% 2.51/1.00  
% 2.51/1.00  fof(f59,plain,(
% 2.51/1.00    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 2.51/1.00    inference(cnf_transformation,[],[f15])).
% 2.51/1.00  
% 2.51/1.00  fof(f5,axiom,(
% 2.51/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 2.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/1.00  
% 2.51/1.00  fof(f23,plain,(
% 2.51/1.00    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 2.51/1.00    inference(ennf_transformation,[],[f5])).
% 2.51/1.00  
% 2.51/1.00  fof(f24,plain,(
% 2.51/1.00    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 2.51/1.00    inference(flattening,[],[f23])).
% 2.51/1.00  
% 2.51/1.00  fof(f48,plain,(
% 2.51/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.51/1.00    inference(cnf_transformation,[],[f24])).
% 2.51/1.00  
% 2.51/1.00  fof(f6,axiom,(
% 2.51/1.00    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 2.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/1.00  
% 2.51/1.00  fof(f25,plain,(
% 2.51/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 2.51/1.00    inference(ennf_transformation,[],[f6])).
% 2.51/1.00  
% 2.51/1.00  fof(f26,plain,(
% 2.51/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.51/1.00    inference(flattening,[],[f25])).
% 2.51/1.00  
% 2.51/1.00  fof(f33,plain,(
% 2.51/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.51/1.00    inference(nnf_transformation,[],[f26])).
% 2.51/1.00  
% 2.51/1.00  fof(f34,plain,(
% 2.51/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.51/1.00    inference(flattening,[],[f33])).
% 2.51/1.00  
% 2.51/1.00  fof(f35,plain,(
% 2.51/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.51/1.00    inference(rectify,[],[f34])).
% 2.51/1.00  
% 2.51/1.00  fof(f36,plain,(
% 2.51/1.00    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK0(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK0(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK0(X0,X1,X2,X3),X1) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))))),
% 2.51/1.00    introduced(choice_axiom,[])).
% 2.51/1.00  
% 2.51/1.00  fof(f37,plain,(
% 2.51/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,sK0(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK0(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK0(X0,X1,X2,X3),X1) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.51/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).
% 2.51/1.00  
% 2.51/1.00  fof(f49,plain,(
% 2.51/1.00    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X3,X1) | k11_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.51/1.00    inference(cnf_transformation,[],[f37])).
% 2.51/1.00  
% 2.51/1.00  fof(f73,plain,(
% 2.51/1.00    ( ! [X2,X0,X1] : (r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1) | ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.51/1.00    inference(equality_resolution,[],[f49])).
% 2.51/1.00  
% 2.51/1.00  fof(f50,plain,(
% 2.51/1.00    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X3,X2) | k11_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.51/1.00    inference(cnf_transformation,[],[f37])).
% 2.51/1.00  
% 2.51/1.00  fof(f72,plain,(
% 2.51/1.00    ( ! [X2,X0,X1] : (r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2) | ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.51/1.00    inference(equality_resolution,[],[f50])).
% 2.51/1.00  
% 2.51/1.00  fof(f1,axiom,(
% 2.51/1.00    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 2.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/1.00  
% 2.51/1.00  fof(f17,plain,(
% 2.51/1.00    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 2.51/1.00    inference(ennf_transformation,[],[f1])).
% 2.51/1.00  
% 2.51/1.00  fof(f18,plain,(
% 2.51/1.00    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 2.51/1.00    inference(flattening,[],[f17])).
% 2.51/1.00  
% 2.51/1.00  fof(f43,plain,(
% 2.51/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.51/1.00    inference(cnf_transformation,[],[f18])).
% 2.51/1.00  
% 2.51/1.00  fof(f2,axiom,(
% 2.51/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/1.00  
% 2.51/1.00  fof(f44,plain,(
% 2.51/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.51/1.00    inference(cnf_transformation,[],[f2])).
% 2.51/1.00  
% 2.51/1.00  fof(f69,plain,(
% 2.51/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.51/1.00    inference(definition_unfolding,[],[f43,f44])).
% 2.51/1.00  
% 2.51/1.00  fof(f68,plain,(
% 2.51/1.00    ~r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k3_xboole_0(sK2,sK3))),
% 2.51/1.00    inference(cnf_transformation,[],[f42])).
% 2.51/1.00  
% 2.51/1.00  fof(f70,plain,(
% 2.51/1.00    ~r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))),
% 2.51/1.00    inference(definition_unfolding,[],[f68,f44])).
% 2.51/1.00  
% 2.51/1.00  cnf(c_22,negated_conjecture,
% 2.51/1.00      ( v2_lattice3(k2_yellow_1(sK1)) ),
% 2.51/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_3,plain,
% 2.51/1.00      ( ~ v2_lattice3(X0) | ~ v2_struct_0(X0) | ~ l1_orders_2(X0) ),
% 2.51/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1,plain,
% 2.51/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 2.51/1.00      | r3_orders_2(X0,X1,X2)
% 2.51/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.51/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.51/1.00      | v2_struct_0(X0)
% 2.51/1.00      | ~ v3_orders_2(X0)
% 2.51/1.00      | ~ l1_orders_2(X0) ),
% 2.51/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_15,plain,
% 2.51/1.00      ( v3_orders_2(k2_yellow_1(X0)) ),
% 2.51/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_368,plain,
% 2.51/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 2.51/1.00      | r3_orders_2(X0,X1,X2)
% 2.51/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.51/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.51/1.00      | v2_struct_0(X0)
% 2.51/1.00      | ~ l1_orders_2(X0)
% 2.51/1.00      | k2_yellow_1(X3) != X0 ),
% 2.51/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_15]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_369,plain,
% 2.51/1.00      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.51/1.00      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.51/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.00      | v2_struct_0(k2_yellow_1(X0))
% 2.51/1.00      | ~ l1_orders_2(k2_yellow_1(X0)) ),
% 2.51/1.00      inference(unflattening,[status(thm)],[c_368]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_13,plain,
% 2.51/1.00      ( l1_orders_2(k2_yellow_1(X0)) ),
% 2.51/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_373,plain,
% 2.51/1.00      ( v2_struct_0(k2_yellow_1(X0))
% 2.51/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.00      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.51/1.00      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2) ),
% 2.51/1.00      inference(global_propositional_subsumption,
% 2.51/1.00                [status(thm)],
% 2.51/1.00                [c_369,c_13]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_374,plain,
% 2.51/1.00      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.51/1.00      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.51/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.00      | v2_struct_0(k2_yellow_1(X0)) ),
% 2.51/1.00      inference(renaming,[status(thm)],[c_373]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_407,plain,
% 2.51/1.00      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.51/1.00      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.51/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.00      | ~ v2_lattice3(X3)
% 2.51/1.00      | ~ l1_orders_2(X3)
% 2.51/1.00      | k2_yellow_1(X0) != X3 ),
% 2.51/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_374]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_408,plain,
% 2.51/1.00      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.51/1.00      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.51/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.00      | ~ v2_lattice3(k2_yellow_1(X0))
% 2.51/1.00      | ~ l1_orders_2(k2_yellow_1(X0)) ),
% 2.51/1.00      inference(unflattening,[status(thm)],[c_407]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_412,plain,
% 2.51/1.00      ( ~ v2_lattice3(k2_yellow_1(X0))
% 2.51/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.00      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.51/1.00      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2) ),
% 2.51/1.00      inference(global_propositional_subsumption,
% 2.51/1.00                [status(thm)],
% 2.51/1.00                [c_408,c_13]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_413,plain,
% 2.51/1.00      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.51/1.00      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.51/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.00      | ~ v2_lattice3(k2_yellow_1(X0)) ),
% 2.51/1.00      inference(renaming,[status(thm)],[c_412]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1084,plain,
% 2.51/1.00      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.51/1.00      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.51/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.00      | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
% 2.51/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_413]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_18,plain,
% 2.51/1.00      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.51/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.00      | r1_tarski(X1,X2)
% 2.51/1.00      | v1_xboole_0(X0) ),
% 2.51/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_23,negated_conjecture,
% 2.51/1.00      ( ~ v1_xboole_0(sK1) ),
% 2.51/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_295,plain,
% 2.51/1.00      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.51/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.00      | r1_tarski(X1,X2)
% 2.51/1.00      | sK1 != X0 ),
% 2.51/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_23]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_296,plain,
% 2.51/1.00      ( ~ r3_orders_2(k2_yellow_1(sK1),X0,X1)
% 2.51/1.00      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 2.51/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
% 2.51/1.00      | r1_tarski(X0,X1) ),
% 2.51/1.00      inference(unflattening,[status(thm)],[c_295]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1194,plain,
% 2.51/1.00      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.51/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.00      | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK1)))
% 2.51/1.00      | ~ m1_subset_1(X4,u1_struct_0(k2_yellow_1(sK1)))
% 2.51/1.00      | r1_tarski(X3,X4)
% 2.51/1.00      | X3 != X1
% 2.51/1.00      | X4 != X2
% 2.51/1.00      | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
% 2.51/1.00      inference(resolution_lifted,[status(thm)],[c_1084,c_296]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1195,plain,
% 2.51/1.00      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.51/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
% 2.51/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK1)))
% 2.51/1.00      | r1_tarski(X1,X2)
% 2.51/1.00      | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
% 2.51/1.00      inference(unflattening,[status(thm)],[c_1194]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_2579,plain,
% 2.51/1.00      ( ~ r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(sK1),sK2,sK3),X1)
% 2.51/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
% 2.51/1.00      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.00      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 2.51/1.00      | r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),X1)
% 2.51/1.00      | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_1195]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_8603,plain,
% 2.51/1.00      ( ~ r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2)
% 2.51/1.00      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 2.51/1.00      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
% 2.51/1.00      | r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2)
% 2.51/1.00      | k2_yellow_1(sK1) != k2_yellow_1(sK1) ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_2579]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1366,plain,( X0 = X0 ),theory(equality) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_7664,plain,
% 2.51/1.00      ( k11_lattice3(k2_yellow_1(sK1),sK2,sK3) = k11_lattice3(k2_yellow_1(sK1),sK2,sK3) ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_1366]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1372,plain,
% 2.51/1.00      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.51/1.00      theory(equality) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_2571,plain,
% 2.51/1.00      ( m1_subset_1(X0,X1)
% 2.51/1.00      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 2.51/1.00      | X0 != k11_lattice3(k2_yellow_1(sK1),sK2,sK3)
% 2.51/1.00      | X1 != u1_struct_0(k2_yellow_1(sK1)) ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_1372]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_7663,plain,
% 2.51/1.00      ( m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),X0)
% 2.51/1.00      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 2.51/1.00      | X0 != u1_struct_0(k2_yellow_1(sK1))
% 2.51/1.00      | k11_lattice3(k2_yellow_1(sK1),sK2,sK3) != k11_lattice3(k2_yellow_1(sK1),sK2,sK3) ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_2571]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_7666,plain,
% 2.51/1.00      ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 2.51/1.00      | m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK1)
% 2.51/1.00      | k11_lattice3(k2_yellow_1(sK1),sK2,sK3) != k11_lattice3(k2_yellow_1(sK1),sK2,sK3)
% 2.51/1.00      | sK1 != u1_struct_0(k2_yellow_1(sK1)) ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_7663]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_20,negated_conjecture,
% 2.51/1.00      ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) ),
% 2.51/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1647,plain,
% 2.51/1.00      ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_16,plain,
% 2.51/1.00      ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
% 2.51/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1655,plain,
% 2.51/1.00      ( m1_subset_1(sK3,sK1) = iProver_top ),
% 2.51/1.00      inference(demodulation,[status(thm)],[c_1647,c_16]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_21,negated_conjecture,
% 2.51/1.00      ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
% 2.51/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1646,plain,
% 2.51/1.00      ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1652,plain,
% 2.51/1.00      ( m1_subset_1(sK2,sK1) = iProver_top ),
% 2.51/1.00      inference(demodulation,[status(thm)],[c_1646,c_16]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_12,plain,
% 2.51/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.51/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.51/1.00      | ~ v5_orders_2(X1)
% 2.51/1.00      | ~ v2_lattice3(X1)
% 2.51/1.00      | ~ l1_orders_2(X1)
% 2.51/1.00      | k11_lattice3(X1,X0,X2) = k11_lattice3(X1,X2,X0) ),
% 2.51/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_14,plain,
% 2.51/1.00      ( v5_orders_2(k2_yellow_1(X0)) ),
% 2.51/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_777,plain,
% 2.51/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.51/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.51/1.00      | ~ v2_lattice3(X1)
% 2.51/1.00      | ~ l1_orders_2(X1)
% 2.51/1.00      | k11_lattice3(X1,X0,X2) = k11_lattice3(X1,X2,X0)
% 2.51/1.00      | k2_yellow_1(X3) != X1 ),
% 2.51/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_14]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_778,plain,
% 2.51/1.00      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
% 2.51/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
% 2.51/1.00      | ~ v2_lattice3(k2_yellow_1(X1))
% 2.51/1.00      | ~ l1_orders_2(k2_yellow_1(X1))
% 2.51/1.00      | k11_lattice3(k2_yellow_1(X1),X2,X0) = k11_lattice3(k2_yellow_1(X1),X0,X2) ),
% 2.51/1.00      inference(unflattening,[status(thm)],[c_777]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_792,plain,
% 2.51/1.00      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
% 2.51/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
% 2.51/1.00      | ~ v2_lattice3(k2_yellow_1(X1))
% 2.51/1.00      | k11_lattice3(k2_yellow_1(X1),X0,X2) = k11_lattice3(k2_yellow_1(X1),X2,X0) ),
% 2.51/1.00      inference(forward_subsumption_resolution,
% 2.51/1.00                [status(thm)],
% 2.51/1.00                [c_778,c_13]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1104,plain,
% 2.51/1.00      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
% 2.51/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
% 2.51/1.00      | k11_lattice3(k2_yellow_1(X1),X0,X2) = k11_lattice3(k2_yellow_1(X1),X2,X0)
% 2.51/1.00      | k2_yellow_1(X1) != k2_yellow_1(sK1) ),
% 2.51/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_792]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1637,plain,
% 2.51/1.00      ( k11_lattice3(k2_yellow_1(X0),X1,X2) = k11_lattice3(k2_yellow_1(X0),X2,X1)
% 2.51/1.00      | k2_yellow_1(X0) != k2_yellow_1(sK1)
% 2.51/1.00      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 2.51/1.00      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_1104]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1673,plain,
% 2.51/1.00      ( k11_lattice3(k2_yellow_1(X0),X1,X2) = k11_lattice3(k2_yellow_1(X0),X2,X1)
% 2.51/1.00      | k2_yellow_1(X0) != k2_yellow_1(sK1)
% 2.51/1.00      | m1_subset_1(X2,X0) != iProver_top
% 2.51/1.00      | m1_subset_1(X1,X0) != iProver_top ),
% 2.51/1.00      inference(light_normalisation,[status(thm)],[c_1637,c_16]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1987,plain,
% 2.51/1.00      ( k11_lattice3(k2_yellow_1(sK1),X0,X1) = k11_lattice3(k2_yellow_1(sK1),X1,X0)
% 2.51/1.00      | m1_subset_1(X0,sK1) != iProver_top
% 2.51/1.00      | m1_subset_1(X1,sK1) != iProver_top ),
% 2.51/1.00      inference(equality_resolution,[status(thm)],[c_1673]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_3285,plain,
% 2.51/1.00      ( k11_lattice3(k2_yellow_1(sK1),sK2,X0) = k11_lattice3(k2_yellow_1(sK1),X0,sK2)
% 2.51/1.00      | m1_subset_1(X0,sK1) != iProver_top ),
% 2.51/1.00      inference(superposition,[status(thm)],[c_1652,c_1987]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_3317,plain,
% 2.51/1.00      ( k11_lattice3(k2_yellow_1(sK1),sK3,sK2) = k11_lattice3(k2_yellow_1(sK1),sK2,sK3) ),
% 2.51/1.00      inference(superposition,[status(thm)],[c_1655,c_3285]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_4,plain,
% 2.51/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.51/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.51/1.00      | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
% 2.51/1.00      | ~ l1_orders_2(X1) ),
% 2.51/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_862,plain,
% 2.51/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.51/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.51/1.00      | m1_subset_1(k11_lattice3(X1,X2,X0),u1_struct_0(X1))
% 2.51/1.00      | k2_yellow_1(X3) != X1 ),
% 2.51/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_13]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_863,plain,
% 2.51/1.00      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
% 2.51/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
% 2.51/1.00      | m1_subset_1(k11_lattice3(k2_yellow_1(X1),X0,X2),u1_struct_0(k2_yellow_1(X1))) ),
% 2.51/1.00      inference(unflattening,[status(thm)],[c_862]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_11,plain,
% 2.51/1.00      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
% 2.51/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.51/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.51/1.00      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.51/1.00      | ~ v5_orders_2(X0)
% 2.51/1.00      | ~ v2_lattice3(X0)
% 2.51/1.00      | v2_struct_0(X0)
% 2.51/1.00      | ~ l1_orders_2(X0) ),
% 2.51/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_138,plain,
% 2.51/1.00      ( ~ v2_lattice3(X0)
% 2.51/1.00      | ~ v5_orders_2(X0)
% 2.51/1.00      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.51/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.51/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.51/1.00      | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
% 2.51/1.00      | ~ l1_orders_2(X0) ),
% 2.51/1.00      inference(global_propositional_subsumption,
% 2.51/1.00                [status(thm)],
% 2.51/1.00                [c_11,c_3]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_139,plain,
% 2.51/1.00      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
% 2.51/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.51/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.51/1.00      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.51/1.00      | ~ v5_orders_2(X0)
% 2.51/1.00      | ~ v2_lattice3(X0)
% 2.51/1.00      | ~ l1_orders_2(X0) ),
% 2.51/1.00      inference(renaming,[status(thm)],[c_138]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_754,plain,
% 2.51/1.00      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
% 2.51/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.51/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.51/1.00      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.51/1.00      | ~ v2_lattice3(X0)
% 2.51/1.00      | ~ l1_orders_2(X0)
% 2.51/1.00      | k2_yellow_1(X3) != X0 ),
% 2.51/1.00      inference(resolution_lifted,[status(thm)],[c_139,c_14]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_755,plain,
% 2.51/1.00      ( r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X1)
% 2.51/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.00      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.00      | ~ v2_lattice3(k2_yellow_1(X0))
% 2.51/1.00      | ~ l1_orders_2(k2_yellow_1(X0)) ),
% 2.51/1.00      inference(unflattening,[status(thm)],[c_754]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_757,plain,
% 2.51/1.00      ( ~ v2_lattice3(k2_yellow_1(X0))
% 2.51/1.00      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.00      | r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X1) ),
% 2.51/1.00      inference(global_propositional_subsumption,
% 2.51/1.00                [status(thm)],
% 2.51/1.00                [c_755,c_13]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_758,plain,
% 2.51/1.00      ( r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X1)
% 2.51/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.00      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.00      | ~ v2_lattice3(k2_yellow_1(X0)) ),
% 2.51/1.00      inference(renaming,[status(thm)],[c_757]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_880,plain,
% 2.51/1.00      ( r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X1)
% 2.51/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.00      | ~ v2_lattice3(k2_yellow_1(X0)) ),
% 2.51/1.00      inference(backward_subsumption_resolution,
% 2.51/1.00                [status(thm)],
% 2.51/1.00                [c_863,c_758]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_904,plain,
% 2.51/1.00      ( r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X1)
% 2.51/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.00      | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
% 2.51/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_880]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1643,plain,
% 2.51/1.00      ( k2_yellow_1(X0) != k2_yellow_1(sK1)
% 2.51/1.00      | r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X1) = iProver_top
% 2.51/1.00      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 2.51/1.00      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_904]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1682,plain,
% 2.51/1.00      ( k2_yellow_1(X0) != k2_yellow_1(sK1)
% 2.51/1.00      | r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X1) = iProver_top
% 2.51/1.00      | m1_subset_1(X1,X0) != iProver_top
% 2.51/1.00      | m1_subset_1(X2,X0) != iProver_top ),
% 2.51/1.00      inference(light_normalisation,[status(thm)],[c_1643,c_16]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_2032,plain,
% 2.51/1.00      ( r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),X0,X1),X0) = iProver_top
% 2.51/1.00      | m1_subset_1(X1,sK1) != iProver_top
% 2.51/1.00      | m1_subset_1(X0,sK1) != iProver_top ),
% 2.51/1.00      inference(equality_resolution,[status(thm)],[c_1682]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_3886,plain,
% 2.51/1.00      ( r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3) = iProver_top
% 2.51/1.00      | m1_subset_1(sK3,sK1) != iProver_top
% 2.51/1.00      | m1_subset_1(sK2,sK1) != iProver_top ),
% 2.51/1.00      inference(superposition,[status(thm)],[c_3317,c_2032]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_26,plain,
% 2.51/1.00      ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_27,plain,
% 2.51/1.00      ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
% 2.51/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1375,plain,
% 2.51/1.00      ( X0 != X1 | k2_yellow_1(X0) = k2_yellow_1(X1) ),
% 2.51/1.00      theory(equality) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1383,plain,
% 2.51/1.00      ( k2_yellow_1(sK1) = k2_yellow_1(sK1) | sK1 != sK1 ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_1375]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_1385,plain,
% 2.51/1.00      ( sK1 = sK1 ),
% 2.51/1.00      inference(instantiation,[status(thm)],[c_1366]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_10,plain,
% 2.51/1.00      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
% 2.51/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.51/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.51/1.00      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.51/1.00      | ~ v5_orders_2(X0)
% 2.51/1.00      | ~ v2_lattice3(X0)
% 2.51/1.00      | v2_struct_0(X0)
% 2.51/1.00      | ~ l1_orders_2(X0) ),
% 2.51/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.51/1.00  
% 2.51/1.00  cnf(c_145,plain,
% 2.51/1.00      ( ~ v2_lattice3(X0)
% 2.51/1.01      | ~ v5_orders_2(X0)
% 2.51/1.01      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.51/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.51/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.51/1.01      | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
% 2.51/1.01      | ~ l1_orders_2(X0) ),
% 2.51/1.01      inference(global_propositional_subsumption,
% 2.51/1.01                [status(thm)],
% 2.51/1.01                [c_10,c_3]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_146,plain,
% 2.51/1.01      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
% 2.51/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.51/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.51/1.01      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.51/1.01      | ~ v5_orders_2(X0)
% 2.51/1.01      | ~ v2_lattice3(X0)
% 2.51/1.01      | ~ l1_orders_2(X0) ),
% 2.51/1.01      inference(renaming,[status(thm)],[c_145]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_727,plain,
% 2.51/1.01      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
% 2.51/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.51/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.51/1.01      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.51/1.01      | ~ v2_lattice3(X0)
% 2.51/1.01      | ~ l1_orders_2(X0)
% 2.51/1.01      | k2_yellow_1(X3) != X0 ),
% 2.51/1.01      inference(resolution_lifted,[status(thm)],[c_146,c_14]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_728,plain,
% 2.51/1.01      ( r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X2)
% 2.51/1.01      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.01      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.01      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.01      | ~ v2_lattice3(k2_yellow_1(X0))
% 2.51/1.01      | ~ l1_orders_2(k2_yellow_1(X0)) ),
% 2.51/1.01      inference(unflattening,[status(thm)],[c_727]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_732,plain,
% 2.51/1.01      ( ~ v2_lattice3(k2_yellow_1(X0))
% 2.51/1.01      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.01      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.01      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.01      | r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X2) ),
% 2.51/1.01      inference(global_propositional_subsumption,
% 2.51/1.01                [status(thm)],
% 2.51/1.01                [c_728,c_13]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_733,plain,
% 2.51/1.01      ( r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X2)
% 2.51/1.01      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.01      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.01      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.01      | ~ v2_lattice3(k2_yellow_1(X0)) ),
% 2.51/1.01      inference(renaming,[status(thm)],[c_732]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_881,plain,
% 2.51/1.01      ( r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X2)
% 2.51/1.01      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.01      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.01      | ~ v2_lattice3(k2_yellow_1(X0)) ),
% 2.51/1.01      inference(backward_subsumption_resolution,
% 2.51/1.01                [status(thm)],
% 2.51/1.01                [c_863,c_733]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_887,plain,
% 2.51/1.01      ( r1_orders_2(k2_yellow_1(X0),k11_lattice3(k2_yellow_1(X0),X1,X2),X2)
% 2.51/1.01      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.01      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.51/1.01      | k2_yellow_1(X0) != k2_yellow_1(sK1) ),
% 2.51/1.01      inference(resolution_lifted,[status(thm)],[c_22,c_881]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1866,plain,
% 2.51/1.01      ( r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),X0,sK3),sK3)
% 2.51/1.01      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 2.51/1.01      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
% 2.51/1.01      | k2_yellow_1(sK1) != k2_yellow_1(sK1) ),
% 2.51/1.01      inference(instantiation,[status(thm)],[c_887]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_2018,plain,
% 2.51/1.01      ( r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3)
% 2.51/1.01      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
% 2.51/1.01      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
% 2.51/1.01      | k2_yellow_1(sK1) != k2_yellow_1(sK1) ),
% 2.51/1.01      inference(instantiation,[status(thm)],[c_1866]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_2019,plain,
% 2.51/1.01      ( k2_yellow_1(sK1) != k2_yellow_1(sK1)
% 2.51/1.01      | r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3) = iProver_top
% 2.51/1.01      | m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
% 2.51/1.01      | m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) != iProver_top ),
% 2.51/1.01      inference(predicate_to_equality,[status(thm)],[c_2018]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_5740,plain,
% 2.51/1.01      ( r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3) = iProver_top ),
% 2.51/1.01      inference(global_propositional_subsumption,
% 2.51/1.01                [status(thm)],
% 2.51/1.01                [c_3886,c_26,c_27,c_1383,c_1385,c_2019]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1636,plain,
% 2.51/1.01      ( k2_yellow_1(X0) != k2_yellow_1(sK1)
% 2.51/1.01      | r1_orders_2(k2_yellow_1(X0),X1,X2) != iProver_top
% 2.51/1.01      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 2.51/1.01      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 2.51/1.01      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
% 2.51/1.01      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
% 2.51/1.01      | r1_tarski(X1,X2) = iProver_top ),
% 2.51/1.01      inference(predicate_to_equality,[status(thm)],[c_1195]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1716,plain,
% 2.51/1.01      ( k2_yellow_1(X0) != k2_yellow_1(sK1)
% 2.51/1.01      | r1_orders_2(k2_yellow_1(X0),X1,X2) != iProver_top
% 2.51/1.01      | m1_subset_1(X1,X0) != iProver_top
% 2.51/1.01      | m1_subset_1(X2,X0) != iProver_top
% 2.51/1.01      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
% 2.51/1.01      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK1))) != iProver_top
% 2.51/1.01      | r1_tarski(X1,X2) = iProver_top ),
% 2.51/1.01      inference(light_normalisation,[status(thm)],[c_1636,c_16]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1717,plain,
% 2.51/1.01      ( k2_yellow_1(X0) != k2_yellow_1(sK1)
% 2.51/1.01      | r1_orders_2(k2_yellow_1(X0),X1,X2) != iProver_top
% 2.51/1.01      | m1_subset_1(X1,X0) != iProver_top
% 2.51/1.01      | m1_subset_1(X2,X0) != iProver_top
% 2.51/1.01      | m1_subset_1(X1,sK1) != iProver_top
% 2.51/1.01      | m1_subset_1(X2,sK1) != iProver_top
% 2.51/1.01      | r1_tarski(X1,X2) = iProver_top ),
% 2.51/1.01      inference(demodulation,[status(thm)],[c_1716,c_16]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_2792,plain,
% 2.51/1.01      ( r1_orders_2(k2_yellow_1(sK1),X0,X1) != iProver_top
% 2.51/1.01      | m1_subset_1(X1,sK1) != iProver_top
% 2.51/1.01      | m1_subset_1(X0,sK1) != iProver_top
% 2.51/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 2.51/1.01      inference(equality_resolution,[status(thm)],[c_1717]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_5745,plain,
% 2.51/1.01      ( m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK1) != iProver_top
% 2.51/1.01      | m1_subset_1(sK3,sK1) != iProver_top
% 2.51/1.01      | r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3) = iProver_top ),
% 2.51/1.01      inference(superposition,[status(thm)],[c_5740,c_2792]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_5746,plain,
% 2.51/1.01      ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK1)
% 2.51/1.01      | ~ m1_subset_1(sK3,sK1)
% 2.51/1.01      | r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3) ),
% 2.51/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_5745]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1367,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_2185,plain,
% 2.51/1.01      ( X0 != X1
% 2.51/1.01      | X0 = u1_struct_0(k2_yellow_1(sK1))
% 2.51/1.01      | u1_struct_0(k2_yellow_1(sK1)) != X1 ),
% 2.51/1.01      inference(instantiation,[status(thm)],[c_1367]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_2186,plain,
% 2.51/1.01      ( u1_struct_0(k2_yellow_1(sK1)) != sK1
% 2.51/1.01      | sK1 = u1_struct_0(k2_yellow_1(sK1))
% 2.51/1.01      | sK1 != sK1 ),
% 2.51/1.01      inference(instantiation,[status(thm)],[c_2185]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_0,plain,
% 2.51/1.01      ( ~ r1_tarski(X0,X1)
% 2.51/1.01      | ~ r1_tarski(X0,X2)
% 2.51/1.01      | r1_tarski(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 2.51/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1649,plain,
% 2.51/1.01      ( r1_tarski(X0,X1) != iProver_top
% 2.51/1.01      | r1_tarski(X0,X2) != iProver_top
% 2.51/1.01      | r1_tarski(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = iProver_top ),
% 2.51/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_19,negated_conjecture,
% 2.51/1.01      ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
% 2.51/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1648,plain,
% 2.51/1.01      ( r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top ),
% 2.51/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_2138,plain,
% 2.51/1.01      ( r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3) != iProver_top
% 2.51/1.01      | r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2) != iProver_top ),
% 2.51/1.01      inference(superposition,[status(thm)],[c_1649,c_1648]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_2139,plain,
% 2.51/1.01      ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK3)
% 2.51/1.01      | ~ r1_tarski(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2) ),
% 2.51/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_2138]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1876,plain,
% 2.51/1.01      ( r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),X0,sK3),X0)
% 2.51/1.01      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 2.51/1.01      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
% 2.51/1.01      | k2_yellow_1(sK1) != k2_yellow_1(sK1) ),
% 2.51/1.01      inference(instantiation,[status(thm)],[c_904]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_2056,plain,
% 2.51/1.01      ( r1_orders_2(k2_yellow_1(sK1),k11_lattice3(k2_yellow_1(sK1),sK2,sK3),sK2)
% 2.51/1.01      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
% 2.51/1.01      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
% 2.51/1.01      | k2_yellow_1(sK1) != k2_yellow_1(sK1) ),
% 2.51/1.01      inference(instantiation,[status(thm)],[c_1876]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1975,plain,
% 2.51/1.01      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 2.51/1.01      | m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,X0),u1_struct_0(k2_yellow_1(sK1)))
% 2.51/1.01      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
% 2.51/1.01      inference(instantiation,[status(thm)],[c_863]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_2049,plain,
% 2.51/1.01      ( m1_subset_1(k11_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 2.51/1.01      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
% 2.51/1.01      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
% 2.51/1.01      inference(instantiation,[status(thm)],[c_1975]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1830,plain,
% 2.51/1.01      ( m1_subset_1(sK3,sK1) ),
% 2.51/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_1655]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_35,plain,
% 2.51/1.01      ( u1_struct_0(k2_yellow_1(sK1)) = sK1 ),
% 2.51/1.01      inference(instantiation,[status(thm)],[c_16]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(contradiction,plain,
% 2.51/1.01      ( $false ),
% 2.51/1.01      inference(minisat,
% 2.51/1.01                [status(thm)],
% 2.51/1.01                [c_8603,c_7664,c_7666,c_5746,c_2186,c_2139,c_2056,c_2049,
% 2.51/1.01                 c_1830,c_1385,c_1383,c_35,c_20,c_21]) ).
% 2.51/1.01  
% 2.51/1.01  
% 2.51/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.51/1.01  
% 2.51/1.01  ------                               Statistics
% 2.51/1.01  
% 2.51/1.01  ------ General
% 2.51/1.01  
% 2.51/1.01  abstr_ref_over_cycles:                  0
% 2.51/1.01  abstr_ref_under_cycles:                 0
% 2.51/1.01  gc_basic_clause_elim:                   0
% 2.51/1.01  forced_gc_time:                         0
% 2.51/1.01  parsing_time:                           0.009
% 2.51/1.01  unif_index_cands_time:                  0.
% 2.51/1.01  unif_index_add_time:                    0.
% 2.51/1.01  orderings_time:                         0.
% 2.51/1.01  out_proof_time:                         0.013
% 2.51/1.01  total_time:                             0.317
% 2.51/1.01  num_of_symbols:                         49
% 2.51/1.01  num_of_terms:                           10707
% 2.51/1.01  
% 2.51/1.01  ------ Preprocessing
% 2.51/1.01  
% 2.51/1.01  num_of_splits:                          0
% 2.51/1.01  num_of_split_atoms:                     0
% 2.51/1.01  num_of_reused_defs:                     0
% 2.51/1.01  num_eq_ax_congr_red:                    14
% 2.51/1.01  num_of_sem_filtered_clauses:            1
% 2.51/1.01  num_of_subtypes:                        0
% 2.51/1.01  monotx_restored_types:                  0
% 2.51/1.01  sat_num_of_epr_types:                   0
% 2.51/1.01  sat_num_of_non_cyclic_types:            0
% 2.51/1.01  sat_guarded_non_collapsed_types:        0
% 2.51/1.01  num_pure_diseq_elim:                    0
% 2.51/1.01  simp_replaced_by:                       0
% 2.51/1.01  res_preprocessed:                       93
% 2.51/1.01  prep_upred:                             0
% 2.51/1.01  prep_unflattend:                        23
% 2.51/1.01  smt_new_axioms:                         0
% 2.51/1.01  pred_elim_cands:                        3
% 2.51/1.01  pred_elim:                              7
% 2.51/1.01  pred_elim_cl:                           8
% 2.51/1.01  pred_elim_cycles:                       10
% 2.51/1.01  merged_defs:                            0
% 2.51/1.01  merged_defs_ncl:                        0
% 2.51/1.01  bin_hyper_res:                          0
% 2.51/1.01  prep_cycles:                            4
% 2.51/1.01  pred_elim_time:                         0.02
% 2.51/1.01  splitting_time:                         0.
% 2.51/1.01  sem_filter_time:                        0.
% 2.51/1.01  monotx_time:                            0.001
% 2.51/1.01  subtype_inf_time:                       0.
% 2.51/1.01  
% 2.51/1.01  ------ Problem properties
% 2.51/1.01  
% 2.51/1.01  clauses:                                16
% 2.51/1.01  conjectures:                            3
% 2.51/1.01  epr:                                    0
% 2.51/1.01  horn:                                   13
% 2.51/1.01  ground:                                 3
% 2.51/1.01  unary:                                  4
% 2.51/1.01  binary:                                 0
% 2.51/1.01  lits:                                   75
% 2.51/1.01  lits_eq:                                16
% 2.51/1.01  fd_pure:                                0
% 2.51/1.01  fd_pseudo:                              0
% 2.51/1.01  fd_cond:                                0
% 2.51/1.01  fd_pseudo_cond:                         4
% 2.51/1.01  ac_symbols:                             0
% 2.51/1.01  
% 2.51/1.01  ------ Propositional Solver
% 2.51/1.01  
% 2.51/1.01  prop_solver_calls:                      28
% 2.51/1.01  prop_fast_solver_calls:                 1327
% 2.51/1.01  smt_solver_calls:                       0
% 2.51/1.01  smt_fast_solver_calls:                  0
% 2.51/1.01  prop_num_of_clauses:                    3511
% 2.51/1.01  prop_preprocess_simplified:             6920
% 2.51/1.01  prop_fo_subsumed:                       20
% 2.51/1.01  prop_solver_time:                       0.
% 2.51/1.01  smt_solver_time:                        0.
% 2.51/1.01  smt_fast_solver_time:                   0.
% 2.51/1.01  prop_fast_solver_time:                  0.
% 2.51/1.01  prop_unsat_core_time:                   0.
% 2.51/1.01  
% 2.51/1.01  ------ QBF
% 2.51/1.01  
% 2.51/1.01  qbf_q_res:                              0
% 2.51/1.01  qbf_num_tautologies:                    0
% 2.51/1.01  qbf_prep_cycles:                        0
% 2.51/1.01  
% 2.51/1.01  ------ BMC1
% 2.51/1.01  
% 2.51/1.01  bmc1_current_bound:                     -1
% 2.51/1.01  bmc1_last_solved_bound:                 -1
% 2.51/1.01  bmc1_unsat_core_size:                   -1
% 2.51/1.01  bmc1_unsat_core_parents_size:           -1
% 2.51/1.01  bmc1_merge_next_fun:                    0
% 2.51/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.51/1.01  
% 2.51/1.01  ------ Instantiation
% 2.51/1.01  
% 2.51/1.01  inst_num_of_clauses:                    883
% 2.51/1.01  inst_num_in_passive:                    124
% 2.51/1.01  inst_num_in_active:                     334
% 2.51/1.01  inst_num_in_unprocessed:                424
% 2.51/1.01  inst_num_of_loops:                      359
% 2.51/1.01  inst_num_of_learning_restarts:          0
% 2.51/1.01  inst_num_moves_active_passive:          22
% 2.51/1.01  inst_lit_activity:                      0
% 2.51/1.01  inst_lit_activity_moves:                1
% 2.51/1.01  inst_num_tautologies:                   0
% 2.51/1.01  inst_num_prop_implied:                  0
% 2.51/1.01  inst_num_existing_simplified:           0
% 2.51/1.01  inst_num_eq_res_simplified:             0
% 2.51/1.01  inst_num_child_elim:                    0
% 2.51/1.01  inst_num_of_dismatching_blockings:      616
% 2.51/1.01  inst_num_of_non_proper_insts:           479
% 2.51/1.01  inst_num_of_duplicates:                 0
% 2.51/1.01  inst_inst_num_from_inst_to_res:         0
% 2.51/1.01  inst_dismatching_checking_time:         0.
% 2.51/1.01  
% 2.51/1.01  ------ Resolution
% 2.51/1.01  
% 2.51/1.01  res_num_of_clauses:                     0
% 2.51/1.01  res_num_in_passive:                     0
% 2.51/1.01  res_num_in_active:                      0
% 2.51/1.01  res_num_of_loops:                       97
% 2.51/1.01  res_forward_subset_subsumed:            97
% 2.51/1.01  res_backward_subset_subsumed:           0
% 2.51/1.01  res_forward_subsumed:                   0
% 2.51/1.01  res_backward_subsumed:                  0
% 2.51/1.01  res_forward_subsumption_resolution:     2
% 2.51/1.01  res_backward_subsumption_resolution:    2
% 2.51/1.01  res_clause_to_clause_subsumption:       927
% 2.51/1.01  res_orphan_elimination:                 0
% 2.51/1.01  res_tautology_del:                      8
% 2.51/1.01  res_num_eq_res_simplified:              0
% 2.51/1.01  res_num_sel_changes:                    0
% 2.51/1.01  res_moves_from_active_to_pass:          0
% 2.51/1.01  
% 2.51/1.01  ------ Superposition
% 2.51/1.01  
% 2.51/1.01  sup_time_total:                         0.
% 2.51/1.01  sup_time_generating:                    0.
% 2.51/1.01  sup_time_sim_full:                      0.
% 2.51/1.01  sup_time_sim_immed:                     0.
% 2.51/1.01  
% 2.51/1.01  sup_num_of_clauses:                     126
% 2.51/1.01  sup_num_in_active:                      70
% 2.51/1.01  sup_num_in_passive:                     56
% 2.51/1.01  sup_num_of_loops:                       70
% 2.51/1.01  sup_fw_superposition:                   97
% 2.51/1.01  sup_bw_superposition:                   73
% 2.51/1.01  sup_immediate_simplified:               72
% 2.51/1.01  sup_given_eliminated:                   0
% 2.51/1.01  comparisons_done:                       0
% 2.51/1.01  comparisons_avoided:                    0
% 2.51/1.01  
% 2.51/1.01  ------ Simplifications
% 2.51/1.01  
% 2.51/1.01  
% 2.51/1.01  sim_fw_subset_subsumed:                 0
% 2.51/1.01  sim_bw_subset_subsumed:                 0
% 2.51/1.01  sim_fw_subsumed:                        53
% 2.51/1.01  sim_bw_subsumed:                        0
% 2.51/1.01  sim_fw_subsumption_res:                 0
% 2.51/1.01  sim_bw_subsumption_res:                 0
% 2.51/1.01  sim_tautology_del:                      1
% 2.51/1.01  sim_eq_tautology_del:                   2
% 2.51/1.01  sim_eq_res_simp:                        0
% 2.51/1.01  sim_fw_demodulated:                     5
% 2.51/1.01  sim_bw_demodulated:                     0
% 2.51/1.01  sim_light_normalised:                   29
% 2.51/1.01  sim_joinable_taut:                      0
% 2.51/1.01  sim_joinable_simp:                      0
% 2.51/1.01  sim_ac_normalised:                      0
% 2.51/1.01  sim_smt_subsumption:                    0
% 2.51/1.01  
%------------------------------------------------------------------------------
