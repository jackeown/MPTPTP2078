%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:20:06 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 327 expanded)
%              Number of clauses        :   70 ( 107 expanded)
%              Number of leaves         :   16 (  75 expanded)
%              Depth                    :   17
%              Number of atoms          :  617 (1476 expanded)
%              Number of equality atoms :   62 (  87 expanded)
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

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_lattice3(k2_yellow_1(X0))
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
               => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( v1_lattice3(k2_yellow_1(X0))
         => ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
                 => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v1_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v1_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))
          & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
     => ( ~ r1_tarski(k2_xboole_0(X1,sK3),k10_lattice3(k2_yellow_1(X0),X1,sK3))
        & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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

fof(f39,plain,
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

fof(f42,plain,
    ( ~ r1_tarski(k2_xboole_0(sK2,sK3),k10_lattice3(k2_yellow_1(sK1),sK2,sK3))
    & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
    & v1_lattice3(k2_yellow_1(sK1))
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f31,f41,f40,f39])).

fof(f64,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f66,plain,(
    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f67,plain,(
    m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f56,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
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
    inference(pure_predicate_removal,[],[f8])).

fof(f15,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f58,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f65,plain,(
    v1_lattice3(k2_yellow_1(sK1)) ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f68,plain,(
    ~ r1_tarski(k2_xboole_0(sK2,sK3),k10_lattice3(k2_yellow_1(sK1),sK2,sK3)) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    ~ r1_tarski(k3_tarski(k2_tarski(sK2,sK3)),k10_lattice3(k2_yellow_1(sK1),sK2,sK3)) ),
    inference(definition_unfolding,[],[f68,f44])).

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

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

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
    inference(nnf_transformation,[],[f21])).

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

fof(f57,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k13_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X2,X4)
                              & r1_orders_2(X0,X1,X4) )
                           => r1_orders_2(X0,X3,X4) ) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k13_lattice3(X0,X1,X2) = X3
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
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k13_lattice3(X0,X1,X2) = X3
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
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
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
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
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
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f33])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
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
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
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

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
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
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | k13_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | k13_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,k13_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ~ v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

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

cnf(c_260,plain,
    ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | r1_tarski(X1,X2)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_23])).

cnf(c_261,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK1),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | r1_tarski(X0,X1) ),
    inference(unflattening,[status(thm)],[c_260])).

cnf(c_2659,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK1),X0,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | r1_tarski(X0,k13_lattice3(k2_yellow_1(sK1),sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_261])).

cnf(c_8330,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK1),sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
    | r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2659])).

cnf(c_8327,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK1),sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    | r1_tarski(sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2659])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2008,plain,
    ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_16,plain,
    ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2018,plain,
    ( m1_subset_1(sK2,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2008,c_16])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2009,plain,
    ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2021,plain,
    ( m1_subset_1(sK3,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2009,c_16])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_12,plain,
    ( l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_735,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0)
    | k2_yellow_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_12])).

cnf(c_736,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | ~ v5_orders_2(k2_yellow_1(X1))
    | ~ v1_lattice3(k2_yellow_1(X1))
    | k10_lattice3(k2_yellow_1(X1),X0,X2) = k13_lattice3(k2_yellow_1(X1),X0,X2) ),
    inference(unflattening,[status(thm)],[c_735])).

cnf(c_13,plain,
    ( v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_750,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | ~ v1_lattice3(k2_yellow_1(X1))
    | k10_lattice3(k2_yellow_1(X1),X0,X2) = k13_lattice3(k2_yellow_1(X1),X0,X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_736,c_13])).

cnf(c_1996,plain,
    ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k13_lattice3(k2_yellow_1(X0),X1,X2)
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | v1_lattice3(k2_yellow_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_750])).

cnf(c_2077,plain,
    ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k13_lattice3(k2_yellow_1(X0),X1,X2)
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | v1_lattice3(k2_yellow_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1996,c_16])).

cnf(c_3096,plain,
    ( k10_lattice3(k2_yellow_1(sK1),X0,sK3) = k13_lattice3(k2_yellow_1(sK1),X0,sK3)
    | m1_subset_1(X0,sK1) != iProver_top
    | v1_lattice3(k2_yellow_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2021,c_2077])).

cnf(c_22,negated_conjecture,
    ( v1_lattice3(k2_yellow_1(sK1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_25,plain,
    ( v1_lattice3(k2_yellow_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4086,plain,
    ( m1_subset_1(X0,sK1) != iProver_top
    | k10_lattice3(k2_yellow_1(sK1),X0,sK3) = k13_lattice3(k2_yellow_1(sK1),X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3096,c_25])).

cnf(c_4087,plain,
    ( k10_lattice3(k2_yellow_1(sK1),X0,sK3) = k13_lattice3(k2_yellow_1(sK1),X0,sK3)
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4086])).

cnf(c_4094,plain,
    ( k10_lattice3(k2_yellow_1(sK1),sK2,sK3) = k13_lattice3(k2_yellow_1(sK1),sK2,sK3) ),
    inference(superposition,[status(thm)],[c_2018,c_4087])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k3_tarski(k2_tarski(X2,X0)),X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2011,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k3_tarski(k2_tarski(X2,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k2_tarski(sK2,sK3)),k10_lattice3(k2_yellow_1(sK1),sK2,sK3)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2010,plain,
    ( r1_tarski(k3_tarski(k2_tarski(sK2,sK3)),k10_lattice3(k2_yellow_1(sK1),sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2912,plain,
    ( r1_tarski(sK3,k10_lattice3(k2_yellow_1(sK1),sK2,sK3)) != iProver_top
    | r1_tarski(sK2,k10_lattice3(k2_yellow_1(sK1),sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2011,c_2010])).

cnf(c_4504,plain,
    ( r1_tarski(sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3)) != iProver_top
    | r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4094,c_2912])).

cnf(c_4512,plain,
    ( ~ r1_tarski(sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
    | ~ r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4504])).

cnf(c_1,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_14,plain,
    ( v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_342,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_14])).

cnf(c_343,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | v2_struct_0(k2_yellow_1(X0))
    | ~ l1_orders_2(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_342])).

cnf(c_347,plain,
    ( v2_struct_0(k2_yellow_1(X0))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r1_orders_2(k2_yellow_1(X0),X1,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_343,c_12])).

cnf(c_348,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | v2_struct_0(k2_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_347])).

cnf(c_2347,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK1),sK2,X0)
    | r3_orders_2(k2_yellow_1(sK1),sK2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
    | v2_struct_0(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_348])).

cnf(c_3868,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK1),sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
    | r3_orders_2(k2_yellow_1(sK1),sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
    | v2_struct_0(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_2347])).

cnf(c_2342,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK1),sK3,X0)
    | r3_orders_2(k2_yellow_1(sK1),sK3,X0)
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    | v2_struct_0(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_348])).

cnf(c_2962,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK1),sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
    | r3_orders_2(k2_yellow_1(sK1),sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    | v2_struct_0(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_2342])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k13_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_758,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k13_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | k2_yellow_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_12])).

cnf(c_759,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | m1_subset_1(k13_lattice3(k2_yellow_1(X1),X0,X2),u1_struct_0(k2_yellow_1(X1)))
    | ~ v5_orders_2(k2_yellow_1(X1))
    | ~ v1_lattice3(k2_yellow_1(X1)) ),
    inference(unflattening,[status(thm)],[c_758])).

cnf(c_773,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | m1_subset_1(k13_lattice3(k2_yellow_1(X1),X0,X2),u1_struct_0(k2_yellow_1(X1)))
    | ~ v1_lattice3(k2_yellow_1(X1)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_759,c_13])).

cnf(c_11,plain,
    ( r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_509,plain,
    ( r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_12])).

cnf(c_510,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,k13_lattice3(k2_yellow_1(X0),X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
    | ~ v5_orders_2(k2_yellow_1(X0))
    | ~ v1_lattice3(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_509])).

cnf(c_514,plain,
    ( ~ m1_subset_1(k13_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | r1_orders_2(k2_yellow_1(X0),X1,k13_lattice3(k2_yellow_1(X0),X1,X2))
    | ~ v1_lattice3(k2_yellow_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_510,c_13])).

cnf(c_515,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,k13_lattice3(k2_yellow_1(X0),X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
    | ~ v1_lattice3(k2_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_514])).

cnf(c_778,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,k13_lattice3(k2_yellow_1(X0),X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ v1_lattice3(k2_yellow_1(X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_773,c_515])).

cnf(c_2323,plain,
    ( r1_orders_2(k2_yellow_1(sK1),sK2,k13_lattice3(k2_yellow_1(sK1),sK2,X0))
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
    | ~ v1_lattice3(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_778])).

cnf(c_2919,plain,
    ( r1_orders_2(k2_yellow_1(sK1),sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
    | ~ v1_lattice3(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_2323])).

cnf(c_10,plain,
    ( r1_orders_2(X0,X1,k13_lattice3(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k13_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_536,plain,
    ( r1_orders_2(X0,X1,k13_lattice3(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k13_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_12])).

cnf(c_537,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,k13_lattice3(k2_yellow_1(X0),X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
    | ~ v5_orders_2(k2_yellow_1(X0))
    | ~ v1_lattice3(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_536])).

cnf(c_539,plain,
    ( ~ m1_subset_1(k13_lattice3(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | r1_orders_2(k2_yellow_1(X0),X1,k13_lattice3(k2_yellow_1(X0),X2,X1))
    | ~ v1_lattice3(k2_yellow_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_537,c_13])).

cnf(c_540,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,k13_lattice3(k2_yellow_1(X0),X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
    | ~ v1_lattice3(k2_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_539])).

cnf(c_777,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,k13_lattice3(k2_yellow_1(X0),X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ v1_lattice3(k2_yellow_1(X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_773,c_540])).

cnf(c_2308,plain,
    ( r1_orders_2(k2_yellow_1(sK1),sK3,k13_lattice3(k2_yellow_1(sK1),X0,sK3))
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    | ~ v1_lattice3(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_777])).

cnf(c_2763,plain,
    ( r1_orders_2(k2_yellow_1(sK1),sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
    | ~ v1_lattice3(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_2308])).

cnf(c_2303,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,X0),u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
    | ~ v1_lattice3(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_773])).

cnf(c_2436,plain,
    ( m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
    | ~ v1_lattice3(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_2303])).

cnf(c_15,plain,
    ( v1_xboole_0(X0)
    | ~ v2_struct_0(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_37,plain,
    ( v1_xboole_0(sK1)
    | ~ v2_struct_0(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8330,c_8327,c_4512,c_3868,c_2962,c_2919,c_2763,c_2436,c_37,c_20,c_21,c_22,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:40:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.97/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/0.99  
% 2.97/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.97/0.99  
% 2.97/0.99  ------  iProver source info
% 2.97/0.99  
% 2.97/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.97/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.97/0.99  git: non_committed_changes: false
% 2.97/0.99  git: last_make_outside_of_git: false
% 2.97/0.99  
% 2.97/0.99  ------ 
% 2.97/0.99  
% 2.97/0.99  ------ Input Options
% 2.97/0.99  
% 2.97/0.99  --out_options                           all
% 2.97/0.99  --tptp_safe_out                         true
% 2.97/0.99  --problem_path                          ""
% 2.97/0.99  --include_path                          ""
% 2.97/0.99  --clausifier                            res/vclausify_rel
% 2.97/0.99  --clausifier_options                    --mode clausify
% 2.97/0.99  --stdin                                 false
% 2.97/0.99  --stats_out                             all
% 2.97/0.99  
% 2.97/0.99  ------ General Options
% 2.97/0.99  
% 2.97/0.99  --fof                                   false
% 2.97/0.99  --time_out_real                         305.
% 2.97/0.99  --time_out_virtual                      -1.
% 2.97/0.99  --symbol_type_check                     false
% 2.97/0.99  --clausify_out                          false
% 2.97/0.99  --sig_cnt_out                           false
% 2.97/0.99  --trig_cnt_out                          false
% 2.97/0.99  --trig_cnt_out_tolerance                1.
% 2.97/0.99  --trig_cnt_out_sk_spl                   false
% 2.97/0.99  --abstr_cl_out                          false
% 2.97/0.99  
% 2.97/0.99  ------ Global Options
% 2.97/0.99  
% 2.97/0.99  --schedule                              default
% 2.97/0.99  --add_important_lit                     false
% 2.97/0.99  --prop_solver_per_cl                    1000
% 2.97/0.99  --min_unsat_core                        false
% 2.97/0.99  --soft_assumptions                      false
% 2.97/0.99  --soft_lemma_size                       3
% 2.97/0.99  --prop_impl_unit_size                   0
% 2.97/0.99  --prop_impl_unit                        []
% 2.97/0.99  --share_sel_clauses                     true
% 2.97/0.99  --reset_solvers                         false
% 2.97/0.99  --bc_imp_inh                            [conj_cone]
% 2.97/0.99  --conj_cone_tolerance                   3.
% 2.97/0.99  --extra_neg_conj                        none
% 2.97/0.99  --large_theory_mode                     true
% 2.97/0.99  --prolific_symb_bound                   200
% 2.97/0.99  --lt_threshold                          2000
% 2.97/0.99  --clause_weak_htbl                      true
% 2.97/0.99  --gc_record_bc_elim                     false
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing Options
% 2.97/0.99  
% 2.97/0.99  --preprocessing_flag                    true
% 2.97/0.99  --time_out_prep_mult                    0.1
% 2.97/0.99  --splitting_mode                        input
% 2.97/0.99  --splitting_grd                         true
% 2.97/0.99  --splitting_cvd                         false
% 2.97/0.99  --splitting_cvd_svl                     false
% 2.97/0.99  --splitting_nvd                         32
% 2.97/0.99  --sub_typing                            true
% 2.97/0.99  --prep_gs_sim                           true
% 2.97/0.99  --prep_unflatten                        true
% 2.97/0.99  --prep_res_sim                          true
% 2.97/0.99  --prep_upred                            true
% 2.97/0.99  --prep_sem_filter                       exhaustive
% 2.97/0.99  --prep_sem_filter_out                   false
% 2.97/0.99  --pred_elim                             true
% 2.97/0.99  --res_sim_input                         true
% 2.97/0.99  --eq_ax_congr_red                       true
% 2.97/0.99  --pure_diseq_elim                       true
% 2.97/0.99  --brand_transform                       false
% 2.97/0.99  --non_eq_to_eq                          false
% 2.97/0.99  --prep_def_merge                        true
% 2.97/0.99  --prep_def_merge_prop_impl              false
% 2.97/0.99  --prep_def_merge_mbd                    true
% 2.97/0.99  --prep_def_merge_tr_red                 false
% 2.97/0.99  --prep_def_merge_tr_cl                  false
% 2.97/0.99  --smt_preprocessing                     true
% 2.97/0.99  --smt_ac_axioms                         fast
% 2.97/0.99  --preprocessed_out                      false
% 2.97/0.99  --preprocessed_stats                    false
% 2.97/0.99  
% 2.97/0.99  ------ Abstraction refinement Options
% 2.97/0.99  
% 2.97/0.99  --abstr_ref                             []
% 2.97/0.99  --abstr_ref_prep                        false
% 2.97/0.99  --abstr_ref_until_sat                   false
% 2.97/0.99  --abstr_ref_sig_restrict                funpre
% 2.97/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.97/0.99  --abstr_ref_under                       []
% 2.97/0.99  
% 2.97/0.99  ------ SAT Options
% 2.97/0.99  
% 2.97/0.99  --sat_mode                              false
% 2.97/0.99  --sat_fm_restart_options                ""
% 2.97/0.99  --sat_gr_def                            false
% 2.97/0.99  --sat_epr_types                         true
% 2.97/0.99  --sat_non_cyclic_types                  false
% 2.97/0.99  --sat_finite_models                     false
% 2.97/0.99  --sat_fm_lemmas                         false
% 2.97/0.99  --sat_fm_prep                           false
% 2.97/0.99  --sat_fm_uc_incr                        true
% 2.97/0.99  --sat_out_model                         small
% 2.97/0.99  --sat_out_clauses                       false
% 2.97/0.99  
% 2.97/0.99  ------ QBF Options
% 2.97/0.99  
% 2.97/0.99  --qbf_mode                              false
% 2.97/0.99  --qbf_elim_univ                         false
% 2.97/0.99  --qbf_dom_inst                          none
% 2.97/0.99  --qbf_dom_pre_inst                      false
% 2.97/0.99  --qbf_sk_in                             false
% 2.97/0.99  --qbf_pred_elim                         true
% 2.97/0.99  --qbf_split                             512
% 2.97/0.99  
% 2.97/0.99  ------ BMC1 Options
% 2.97/0.99  
% 2.97/0.99  --bmc1_incremental                      false
% 2.97/0.99  --bmc1_axioms                           reachable_all
% 2.97/0.99  --bmc1_min_bound                        0
% 2.97/0.99  --bmc1_max_bound                        -1
% 2.97/0.99  --bmc1_max_bound_default                -1
% 2.97/0.99  --bmc1_symbol_reachability              true
% 2.97/0.99  --bmc1_property_lemmas                  false
% 2.97/0.99  --bmc1_k_induction                      false
% 2.97/0.99  --bmc1_non_equiv_states                 false
% 2.97/0.99  --bmc1_deadlock                         false
% 2.97/0.99  --bmc1_ucm                              false
% 2.97/0.99  --bmc1_add_unsat_core                   none
% 2.97/0.99  --bmc1_unsat_core_children              false
% 2.97/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.97/0.99  --bmc1_out_stat                         full
% 2.97/0.99  --bmc1_ground_init                      false
% 2.97/0.99  --bmc1_pre_inst_next_state              false
% 2.97/0.99  --bmc1_pre_inst_state                   false
% 2.97/0.99  --bmc1_pre_inst_reach_state             false
% 2.97/0.99  --bmc1_out_unsat_core                   false
% 2.97/0.99  --bmc1_aig_witness_out                  false
% 2.97/0.99  --bmc1_verbose                          false
% 2.97/0.99  --bmc1_dump_clauses_tptp                false
% 2.97/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.97/0.99  --bmc1_dump_file                        -
% 2.97/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.97/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.97/0.99  --bmc1_ucm_extend_mode                  1
% 2.97/0.99  --bmc1_ucm_init_mode                    2
% 2.97/0.99  --bmc1_ucm_cone_mode                    none
% 2.97/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.97/0.99  --bmc1_ucm_relax_model                  4
% 2.97/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.97/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.97/0.99  --bmc1_ucm_layered_model                none
% 2.97/0.99  --bmc1_ucm_max_lemma_size               10
% 2.97/0.99  
% 2.97/0.99  ------ AIG Options
% 2.97/0.99  
% 2.97/0.99  --aig_mode                              false
% 2.97/0.99  
% 2.97/0.99  ------ Instantiation Options
% 2.97/0.99  
% 2.97/0.99  --instantiation_flag                    true
% 2.97/0.99  --inst_sos_flag                         false
% 2.97/0.99  --inst_sos_phase                        true
% 2.97/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.97/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.97/0.99  --inst_lit_sel_side                     num_symb
% 2.97/0.99  --inst_solver_per_active                1400
% 2.97/0.99  --inst_solver_calls_frac                1.
% 2.97/0.99  --inst_passive_queue_type               priority_queues
% 2.97/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.97/0.99  --inst_passive_queues_freq              [25;2]
% 2.97/0.99  --inst_dismatching                      true
% 2.97/0.99  --inst_eager_unprocessed_to_passive     true
% 2.97/0.99  --inst_prop_sim_given                   true
% 2.97/0.99  --inst_prop_sim_new                     false
% 2.97/0.99  --inst_subs_new                         false
% 2.97/0.99  --inst_eq_res_simp                      false
% 2.97/0.99  --inst_subs_given                       false
% 2.97/0.99  --inst_orphan_elimination               true
% 2.97/0.99  --inst_learning_loop_flag               true
% 2.97/0.99  --inst_learning_start                   3000
% 2.97/0.99  --inst_learning_factor                  2
% 2.97/0.99  --inst_start_prop_sim_after_learn       3
% 2.97/0.99  --inst_sel_renew                        solver
% 2.97/0.99  --inst_lit_activity_flag                true
% 2.97/0.99  --inst_restr_to_given                   false
% 2.97/0.99  --inst_activity_threshold               500
% 2.97/0.99  --inst_out_proof                        true
% 2.97/0.99  
% 2.97/0.99  ------ Resolution Options
% 2.97/0.99  
% 2.97/0.99  --resolution_flag                       true
% 2.97/0.99  --res_lit_sel                           adaptive
% 2.97/0.99  --res_lit_sel_side                      none
% 2.97/0.99  --res_ordering                          kbo
% 2.97/0.99  --res_to_prop_solver                    active
% 2.97/0.99  --res_prop_simpl_new                    false
% 2.97/0.99  --res_prop_simpl_given                  true
% 2.97/0.99  --res_passive_queue_type                priority_queues
% 2.97/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.97/0.99  --res_passive_queues_freq               [15;5]
% 2.97/0.99  --res_forward_subs                      full
% 2.97/0.99  --res_backward_subs                     full
% 2.97/0.99  --res_forward_subs_resolution           true
% 2.97/0.99  --res_backward_subs_resolution          true
% 2.97/0.99  --res_orphan_elimination                true
% 2.97/0.99  --res_time_limit                        2.
% 2.97/0.99  --res_out_proof                         true
% 2.97/0.99  
% 2.97/0.99  ------ Superposition Options
% 2.97/0.99  
% 2.97/0.99  --superposition_flag                    true
% 2.97/0.99  --sup_passive_queue_type                priority_queues
% 2.97/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.97/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.97/0.99  --demod_completeness_check              fast
% 2.97/0.99  --demod_use_ground                      true
% 2.97/0.99  --sup_to_prop_solver                    passive
% 2.97/0.99  --sup_prop_simpl_new                    true
% 2.97/0.99  --sup_prop_simpl_given                  true
% 2.97/0.99  --sup_fun_splitting                     false
% 2.97/0.99  --sup_smt_interval                      50000
% 2.97/0.99  
% 2.97/0.99  ------ Superposition Simplification Setup
% 2.97/0.99  
% 2.97/0.99  --sup_indices_passive                   []
% 2.97/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.97/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_full_bw                           [BwDemod]
% 2.97/0.99  --sup_immed_triv                        [TrivRules]
% 2.97/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.97/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_immed_bw_main                     []
% 2.97/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.97/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.99  
% 2.97/0.99  ------ Combination Options
% 2.97/0.99  
% 2.97/0.99  --comb_res_mult                         3
% 2.97/0.99  --comb_sup_mult                         2
% 2.97/0.99  --comb_inst_mult                        10
% 2.97/0.99  
% 2.97/0.99  ------ Debug Options
% 2.97/0.99  
% 2.97/0.99  --dbg_backtrace                         false
% 2.97/0.99  --dbg_dump_prop_clauses                 false
% 2.97/0.99  --dbg_dump_prop_clauses_file            -
% 2.97/0.99  --dbg_out_stat                          false
% 2.97/0.99  ------ Parsing...
% 2.97/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.97/0.99  ------ Proving...
% 2.97/0.99  ------ Problem Properties 
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  clauses                                 20
% 2.97/0.99  conjectures                             4
% 2.97/0.99  EPR                                     0
% 2.97/0.99  Horn                                    15
% 2.97/0.99  unary                                   6
% 2.97/0.99  binary                                  0
% 2.97/0.99  lits                                    83
% 2.97/0.99  lits eq                                 6
% 2.97/0.99  fd_pure                                 0
% 2.97/0.99  fd_pseudo                               0
% 2.97/0.99  fd_cond                                 0
% 2.97/0.99  fd_pseudo_cond                          4
% 2.97/0.99  AC symbols                              0
% 2.97/0.99  
% 2.97/0.99  ------ Schedule dynamic 5 is on 
% 2.97/0.99  
% 2.97/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  ------ 
% 2.97/0.99  Current options:
% 2.97/0.99  ------ 
% 2.97/0.99  
% 2.97/0.99  ------ Input Options
% 2.97/0.99  
% 2.97/0.99  --out_options                           all
% 2.97/0.99  --tptp_safe_out                         true
% 2.97/0.99  --problem_path                          ""
% 2.97/0.99  --include_path                          ""
% 2.97/0.99  --clausifier                            res/vclausify_rel
% 2.97/0.99  --clausifier_options                    --mode clausify
% 2.97/0.99  --stdin                                 false
% 2.97/0.99  --stats_out                             all
% 2.97/0.99  
% 2.97/0.99  ------ General Options
% 2.97/0.99  
% 2.97/0.99  --fof                                   false
% 2.97/0.99  --time_out_real                         305.
% 2.97/0.99  --time_out_virtual                      -1.
% 2.97/0.99  --symbol_type_check                     false
% 2.97/0.99  --clausify_out                          false
% 2.97/0.99  --sig_cnt_out                           false
% 2.97/0.99  --trig_cnt_out                          false
% 2.97/0.99  --trig_cnt_out_tolerance                1.
% 2.97/0.99  --trig_cnt_out_sk_spl                   false
% 2.97/0.99  --abstr_cl_out                          false
% 2.97/0.99  
% 2.97/0.99  ------ Global Options
% 2.97/0.99  
% 2.97/0.99  --schedule                              default
% 2.97/0.99  --add_important_lit                     false
% 2.97/0.99  --prop_solver_per_cl                    1000
% 2.97/0.99  --min_unsat_core                        false
% 2.97/0.99  --soft_assumptions                      false
% 2.97/0.99  --soft_lemma_size                       3
% 2.97/0.99  --prop_impl_unit_size                   0
% 2.97/0.99  --prop_impl_unit                        []
% 2.97/0.99  --share_sel_clauses                     true
% 2.97/0.99  --reset_solvers                         false
% 2.97/0.99  --bc_imp_inh                            [conj_cone]
% 2.97/0.99  --conj_cone_tolerance                   3.
% 2.97/0.99  --extra_neg_conj                        none
% 2.97/0.99  --large_theory_mode                     true
% 2.97/0.99  --prolific_symb_bound                   200
% 2.97/0.99  --lt_threshold                          2000
% 2.97/0.99  --clause_weak_htbl                      true
% 2.97/0.99  --gc_record_bc_elim                     false
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing Options
% 2.97/0.99  
% 2.97/0.99  --preprocessing_flag                    true
% 2.97/0.99  --time_out_prep_mult                    0.1
% 2.97/0.99  --splitting_mode                        input
% 2.97/0.99  --splitting_grd                         true
% 2.97/0.99  --splitting_cvd                         false
% 2.97/0.99  --splitting_cvd_svl                     false
% 2.97/0.99  --splitting_nvd                         32
% 2.97/0.99  --sub_typing                            true
% 2.97/0.99  --prep_gs_sim                           true
% 2.97/0.99  --prep_unflatten                        true
% 2.97/0.99  --prep_res_sim                          true
% 2.97/0.99  --prep_upred                            true
% 2.97/0.99  --prep_sem_filter                       exhaustive
% 2.97/0.99  --prep_sem_filter_out                   false
% 2.97/0.99  --pred_elim                             true
% 2.97/0.99  --res_sim_input                         true
% 2.97/0.99  --eq_ax_congr_red                       true
% 2.97/0.99  --pure_diseq_elim                       true
% 2.97/0.99  --brand_transform                       false
% 2.97/0.99  --non_eq_to_eq                          false
% 2.97/0.99  --prep_def_merge                        true
% 2.97/0.99  --prep_def_merge_prop_impl              false
% 2.97/0.99  --prep_def_merge_mbd                    true
% 2.97/0.99  --prep_def_merge_tr_red                 false
% 2.97/0.99  --prep_def_merge_tr_cl                  false
% 2.97/0.99  --smt_preprocessing                     true
% 2.97/0.99  --smt_ac_axioms                         fast
% 2.97/0.99  --preprocessed_out                      false
% 2.97/0.99  --preprocessed_stats                    false
% 2.97/0.99  
% 2.97/0.99  ------ Abstraction refinement Options
% 2.97/0.99  
% 2.97/0.99  --abstr_ref                             []
% 2.97/0.99  --abstr_ref_prep                        false
% 2.97/0.99  --abstr_ref_until_sat                   false
% 2.97/0.99  --abstr_ref_sig_restrict                funpre
% 2.97/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.97/0.99  --abstr_ref_under                       []
% 2.97/0.99  
% 2.97/0.99  ------ SAT Options
% 2.97/0.99  
% 2.97/0.99  --sat_mode                              false
% 2.97/0.99  --sat_fm_restart_options                ""
% 2.97/0.99  --sat_gr_def                            false
% 2.97/0.99  --sat_epr_types                         true
% 2.97/0.99  --sat_non_cyclic_types                  false
% 2.97/0.99  --sat_finite_models                     false
% 2.97/0.99  --sat_fm_lemmas                         false
% 2.97/0.99  --sat_fm_prep                           false
% 2.97/0.99  --sat_fm_uc_incr                        true
% 2.97/0.99  --sat_out_model                         small
% 2.97/0.99  --sat_out_clauses                       false
% 2.97/0.99  
% 2.97/0.99  ------ QBF Options
% 2.97/0.99  
% 2.97/0.99  --qbf_mode                              false
% 2.97/0.99  --qbf_elim_univ                         false
% 2.97/0.99  --qbf_dom_inst                          none
% 2.97/0.99  --qbf_dom_pre_inst                      false
% 2.97/0.99  --qbf_sk_in                             false
% 2.97/0.99  --qbf_pred_elim                         true
% 2.97/0.99  --qbf_split                             512
% 2.97/0.99  
% 2.97/0.99  ------ BMC1 Options
% 2.97/0.99  
% 2.97/0.99  --bmc1_incremental                      false
% 2.97/0.99  --bmc1_axioms                           reachable_all
% 2.97/0.99  --bmc1_min_bound                        0
% 2.97/0.99  --bmc1_max_bound                        -1
% 2.97/0.99  --bmc1_max_bound_default                -1
% 2.97/0.99  --bmc1_symbol_reachability              true
% 2.97/0.99  --bmc1_property_lemmas                  false
% 2.97/0.99  --bmc1_k_induction                      false
% 2.97/0.99  --bmc1_non_equiv_states                 false
% 2.97/0.99  --bmc1_deadlock                         false
% 2.97/0.99  --bmc1_ucm                              false
% 2.97/0.99  --bmc1_add_unsat_core                   none
% 2.97/0.99  --bmc1_unsat_core_children              false
% 2.97/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.97/0.99  --bmc1_out_stat                         full
% 2.97/0.99  --bmc1_ground_init                      false
% 2.97/0.99  --bmc1_pre_inst_next_state              false
% 2.97/0.99  --bmc1_pre_inst_state                   false
% 2.97/0.99  --bmc1_pre_inst_reach_state             false
% 2.97/0.99  --bmc1_out_unsat_core                   false
% 2.97/0.99  --bmc1_aig_witness_out                  false
% 2.97/0.99  --bmc1_verbose                          false
% 2.97/0.99  --bmc1_dump_clauses_tptp                false
% 2.97/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.97/0.99  --bmc1_dump_file                        -
% 2.97/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.97/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.97/0.99  --bmc1_ucm_extend_mode                  1
% 2.97/0.99  --bmc1_ucm_init_mode                    2
% 2.97/0.99  --bmc1_ucm_cone_mode                    none
% 2.97/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.97/0.99  --bmc1_ucm_relax_model                  4
% 2.97/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.97/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.97/0.99  --bmc1_ucm_layered_model                none
% 2.97/0.99  --bmc1_ucm_max_lemma_size               10
% 2.97/0.99  
% 2.97/0.99  ------ AIG Options
% 2.97/0.99  
% 2.97/0.99  --aig_mode                              false
% 2.97/0.99  
% 2.97/0.99  ------ Instantiation Options
% 2.97/0.99  
% 2.97/0.99  --instantiation_flag                    true
% 2.97/0.99  --inst_sos_flag                         false
% 2.97/0.99  --inst_sos_phase                        true
% 2.97/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.97/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.97/0.99  --inst_lit_sel_side                     none
% 2.97/0.99  --inst_solver_per_active                1400
% 2.97/0.99  --inst_solver_calls_frac                1.
% 2.97/0.99  --inst_passive_queue_type               priority_queues
% 2.97/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.97/0.99  --inst_passive_queues_freq              [25;2]
% 2.97/0.99  --inst_dismatching                      true
% 2.97/0.99  --inst_eager_unprocessed_to_passive     true
% 2.97/0.99  --inst_prop_sim_given                   true
% 2.97/0.99  --inst_prop_sim_new                     false
% 2.97/0.99  --inst_subs_new                         false
% 2.97/0.99  --inst_eq_res_simp                      false
% 2.97/0.99  --inst_subs_given                       false
% 2.97/0.99  --inst_orphan_elimination               true
% 2.97/0.99  --inst_learning_loop_flag               true
% 2.97/0.99  --inst_learning_start                   3000
% 2.97/0.99  --inst_learning_factor                  2
% 2.97/0.99  --inst_start_prop_sim_after_learn       3
% 2.97/0.99  --inst_sel_renew                        solver
% 2.97/0.99  --inst_lit_activity_flag                true
% 2.97/0.99  --inst_restr_to_given                   false
% 2.97/0.99  --inst_activity_threshold               500
% 2.97/0.99  --inst_out_proof                        true
% 2.97/0.99  
% 2.97/0.99  ------ Resolution Options
% 2.97/0.99  
% 2.97/0.99  --resolution_flag                       false
% 2.97/0.99  --res_lit_sel                           adaptive
% 2.97/0.99  --res_lit_sel_side                      none
% 2.97/0.99  --res_ordering                          kbo
% 2.97/0.99  --res_to_prop_solver                    active
% 2.97/0.99  --res_prop_simpl_new                    false
% 2.97/0.99  --res_prop_simpl_given                  true
% 2.97/0.99  --res_passive_queue_type                priority_queues
% 2.97/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.97/0.99  --res_passive_queues_freq               [15;5]
% 2.97/0.99  --res_forward_subs                      full
% 2.97/0.99  --res_backward_subs                     full
% 2.97/0.99  --res_forward_subs_resolution           true
% 2.97/0.99  --res_backward_subs_resolution          true
% 2.97/0.99  --res_orphan_elimination                true
% 2.97/0.99  --res_time_limit                        2.
% 2.97/0.99  --res_out_proof                         true
% 2.97/0.99  
% 2.97/0.99  ------ Superposition Options
% 2.97/0.99  
% 2.97/0.99  --superposition_flag                    true
% 2.97/0.99  --sup_passive_queue_type                priority_queues
% 2.97/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.97/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.97/0.99  --demod_completeness_check              fast
% 2.97/0.99  --demod_use_ground                      true
% 2.97/0.99  --sup_to_prop_solver                    passive
% 2.97/0.99  --sup_prop_simpl_new                    true
% 2.97/0.99  --sup_prop_simpl_given                  true
% 2.97/0.99  --sup_fun_splitting                     false
% 2.97/0.99  --sup_smt_interval                      50000
% 2.97/0.99  
% 2.97/0.99  ------ Superposition Simplification Setup
% 2.97/0.99  
% 2.97/0.99  --sup_indices_passive                   []
% 2.97/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.97/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_full_bw                           [BwDemod]
% 2.97/0.99  --sup_immed_triv                        [TrivRules]
% 2.97/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.97/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_immed_bw_main                     []
% 2.97/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.97/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.99  
% 2.97/0.99  ------ Combination Options
% 2.97/0.99  
% 2.97/0.99  --comb_res_mult                         3
% 2.97/0.99  --comb_sup_mult                         2
% 2.97/0.99  --comb_inst_mult                        10
% 2.97/0.99  
% 2.97/0.99  ------ Debug Options
% 2.97/0.99  
% 2.97/0.99  --dbg_backtrace                         false
% 2.97/0.99  --dbg_dump_prop_clauses                 false
% 2.97/0.99  --dbg_dump_prop_clauses_file            -
% 2.97/0.99  --dbg_out_stat                          false
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  ------ Proving...
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  % SZS status Theorem for theBenchmark.p
% 2.97/0.99  
% 2.97/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.97/0.99  
% 2.97/0.99  fof(f11,axiom,(
% 2.97/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f29,plain,(
% 2.97/0.99    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 2.97/0.99    inference(ennf_transformation,[],[f11])).
% 2.97/0.99  
% 2.97/0.99  fof(f38,plain,(
% 2.97/0.99    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 2.97/0.99    inference(nnf_transformation,[],[f29])).
% 2.97/0.99  
% 2.97/0.99  fof(f62,plain,(
% 2.97/0.99    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f38])).
% 2.97/0.99  
% 2.97/0.99  fof(f12,conjecture,(
% 2.97/0.99    ! [X0] : (~v1_xboole_0(X0) => (v1_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))))))),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f13,negated_conjecture,(
% 2.97/0.99    ~! [X0] : (~v1_xboole_0(X0) => (v1_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))))))),
% 2.97/0.99    inference(negated_conjecture,[],[f12])).
% 2.97/0.99  
% 2.97/0.99  fof(f30,plain,(
% 2.97/0.99    ? [X0] : ((? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v1_lattice3(k2_yellow_1(X0))) & ~v1_xboole_0(X0))),
% 2.97/0.99    inference(ennf_transformation,[],[f13])).
% 2.97/0.99  
% 2.97/0.99  fof(f31,plain,(
% 2.97/0.99    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v1_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0))),
% 2.97/0.99    inference(flattening,[],[f30])).
% 2.97/0.99  
% 2.97/0.99  fof(f41,plain,(
% 2.97/0.99    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) => (~r1_tarski(k2_xboole_0(X1,sK3),k10_lattice3(k2_yellow_1(X0),X1,sK3)) & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0))))) )),
% 2.97/0.99    introduced(choice_axiom,[])).
% 2.97/0.99  
% 2.97/0.99  fof(f40,plain,(
% 2.97/0.99    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) => (? [X2] : (~r1_tarski(k2_xboole_0(sK2,X2),k10_lattice3(k2_yellow_1(X0),sK2,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(X0))))) )),
% 2.97/0.99    introduced(choice_axiom,[])).
% 2.97/0.99  
% 2.97/0.99  fof(f39,plain,(
% 2.97/0.99    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v1_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(sK1),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK1)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))) & v1_lattice3(k2_yellow_1(sK1)) & ~v1_xboole_0(sK1))),
% 2.97/0.99    introduced(choice_axiom,[])).
% 2.97/0.99  
% 2.97/0.99  fof(f42,plain,(
% 2.97/0.99    ((~r1_tarski(k2_xboole_0(sK2,sK3),k10_lattice3(k2_yellow_1(sK1),sK2,sK3)) & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))) & v1_lattice3(k2_yellow_1(sK1)) & ~v1_xboole_0(sK1)),
% 2.97/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f31,f41,f40,f39])).
% 2.97/0.99  
% 2.97/0.99  fof(f64,plain,(
% 2.97/0.99    ~v1_xboole_0(sK1)),
% 2.97/0.99    inference(cnf_transformation,[],[f42])).
% 2.97/0.99  
% 2.97/0.99  fof(f66,plain,(
% 2.97/0.99    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))),
% 2.97/0.99    inference(cnf_transformation,[],[f42])).
% 2.97/0.99  
% 2.97/0.99  fof(f10,axiom,(
% 2.97/0.99    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f60,plain,(
% 2.97/0.99    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 2.97/0.99    inference(cnf_transformation,[],[f10])).
% 2.97/0.99  
% 2.97/0.99  fof(f67,plain,(
% 2.97/0.99    m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))),
% 2.97/0.99    inference(cnf_transformation,[],[f42])).
% 2.97/0.99  
% 2.97/0.99  fof(f5,axiom,(
% 2.97/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2))),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f24,plain,(
% 2.97/0.99    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 2.97/1.00    inference(ennf_transformation,[],[f5])).
% 2.97/1.00  
% 2.97/1.00  fof(f25,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 2.97/1.00    inference(flattening,[],[f24])).
% 2.97/1.00  
% 2.97/1.00  fof(f48,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f25])).
% 2.97/1.00  
% 2.97/1.00  fof(f7,axiom,(
% 2.97/1.00    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 2.97/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f16,plain,(
% 2.97/1.00    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 2.97/1.00    inference(pure_predicate_removal,[],[f7])).
% 2.97/1.00  
% 2.97/1.00  fof(f56,plain,(
% 2.97/1.00    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 2.97/1.00    inference(cnf_transformation,[],[f16])).
% 2.97/1.00  
% 2.97/1.00  fof(f8,axiom,(
% 2.97/1.00    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 2.97/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f14,plain,(
% 2.97/1.00    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 2.97/1.00    inference(pure_predicate_removal,[],[f8])).
% 2.97/1.00  
% 2.97/1.00  fof(f15,plain,(
% 2.97/1.00    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 2.97/1.00    inference(pure_predicate_removal,[],[f14])).
% 2.97/1.00  
% 2.97/1.00  fof(f58,plain,(
% 2.97/1.00    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 2.97/1.00    inference(cnf_transformation,[],[f15])).
% 2.97/1.00  
% 2.97/1.00  fof(f65,plain,(
% 2.97/1.00    v1_lattice3(k2_yellow_1(sK1))),
% 2.97/1.00    inference(cnf_transformation,[],[f42])).
% 2.97/1.00  
% 2.97/1.00  fof(f1,axiom,(
% 2.97/1.00    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 2.97/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f18,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 2.97/1.00    inference(ennf_transformation,[],[f1])).
% 2.97/1.00  
% 2.97/1.00  fof(f19,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 2.97/1.00    inference(flattening,[],[f18])).
% 2.97/1.00  
% 2.97/1.00  fof(f43,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f19])).
% 2.97/1.00  
% 2.97/1.00  fof(f2,axiom,(
% 2.97/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.97/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f44,plain,(
% 2.97/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.97/1.00    inference(cnf_transformation,[],[f2])).
% 2.97/1.00  
% 2.97/1.00  fof(f69,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.97/1.00    inference(definition_unfolding,[],[f43,f44])).
% 2.97/1.00  
% 2.97/1.00  fof(f68,plain,(
% 2.97/1.00    ~r1_tarski(k2_xboole_0(sK2,sK3),k10_lattice3(k2_yellow_1(sK1),sK2,sK3))),
% 2.97/1.00    inference(cnf_transformation,[],[f42])).
% 2.97/1.00  
% 2.97/1.00  fof(f70,plain,(
% 2.97/1.00    ~r1_tarski(k3_tarski(k2_tarski(sK2,sK3)),k10_lattice3(k2_yellow_1(sK1),sK2,sK3))),
% 2.97/1.00    inference(definition_unfolding,[],[f68,f44])).
% 2.97/1.00  
% 2.97/1.00  fof(f3,axiom,(
% 2.97/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 2.97/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f20,plain,(
% 2.97/1.00    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.97/1.00    inference(ennf_transformation,[],[f3])).
% 2.97/1.00  
% 2.97/1.00  fof(f21,plain,(
% 2.97/1.00    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.97/1.00    inference(flattening,[],[f20])).
% 2.97/1.00  
% 2.97/1.00  fof(f32,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.97/1.00    inference(nnf_transformation,[],[f21])).
% 2.97/1.00  
% 2.97/1.00  fof(f46,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f32])).
% 2.97/1.00  
% 2.97/1.00  fof(f57,plain,(
% 2.97/1.00    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 2.97/1.00    inference(cnf_transformation,[],[f15])).
% 2.97/1.00  
% 2.97/1.00  fof(f4,axiom,(
% 2.97/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 2.97/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f22,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 2.97/1.00    inference(ennf_transformation,[],[f4])).
% 2.97/1.00  
% 2.97/1.00  fof(f23,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 2.97/1.00    inference(flattening,[],[f22])).
% 2.97/1.00  
% 2.97/1.00  fof(f47,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f23])).
% 2.97/1.00  
% 2.97/1.00  fof(f6,axiom,(
% 2.97/1.00    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k13_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 2.97/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f26,plain,(
% 2.97/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k13_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 2.97/1.00    inference(ennf_transformation,[],[f6])).
% 2.97/1.00  
% 2.97/1.00  fof(f27,plain,(
% 2.97/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k13_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 2.97/1.00    inference(flattening,[],[f26])).
% 2.97/1.00  
% 2.97/1.00  fof(f33,plain,(
% 2.97/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k13_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3))) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k13_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 2.97/1.00    inference(nnf_transformation,[],[f27])).
% 2.97/1.00  
% 2.97/1.00  fof(f34,plain,(
% 2.97/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k13_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k13_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 2.97/1.00    inference(flattening,[],[f33])).
% 2.97/1.00  
% 2.97/1.00  fof(f35,plain,(
% 2.97/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k13_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k13_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 2.97/1.00    inference(rectify,[],[f34])).
% 2.97/1.00  
% 2.97/1.00  fof(f36,plain,(
% 2.97/1.00    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,X3,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))))),
% 2.97/1.00    introduced(choice_axiom,[])).
% 2.97/1.00  
% 2.97/1.00  fof(f37,plain,(
% 2.97/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k13_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,X3,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k13_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 2.97/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).
% 2.97/1.00  
% 2.97/1.00  fof(f49,plain,(
% 2.97/1.00    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X1,X3) | k13_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f37])).
% 2.97/1.00  
% 2.97/1.00  fof(f73,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2)) | ~m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 2.97/1.00    inference(equality_resolution,[],[f49])).
% 2.97/1.00  
% 2.97/1.00  fof(f50,plain,(
% 2.97/1.00    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X2,X3) | k13_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f37])).
% 2.97/1.00  
% 2.97/1.00  fof(f72,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (r1_orders_2(X0,X2,k13_lattice3(X0,X1,X2)) | ~m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 2.97/1.00    inference(equality_resolution,[],[f50])).
% 2.97/1.00  
% 2.97/1.00  fof(f9,axiom,(
% 2.97/1.00    ! [X0] : (~v1_xboole_0(X0) => (v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))))),
% 2.97/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f17,plain,(
% 2.97/1.00    ! [X0] : (~v1_xboole_0(X0) => ~v2_struct_0(k2_yellow_1(X0)))),
% 2.97/1.00    inference(pure_predicate_removal,[],[f9])).
% 2.97/1.00  
% 2.97/1.00  fof(f28,plain,(
% 2.97/1.00    ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0))),
% 2.97/1.00    inference(ennf_transformation,[],[f17])).
% 2.97/1.00  
% 2.97/1.00  fof(f59,plain,(
% 2.97/1.00    ( ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f28])).
% 2.97/1.00  
% 2.97/1.00  cnf(c_18,plain,
% 2.97/1.00      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.97/1.00      | r1_tarski(X1,X2)
% 2.97/1.00      | v1_xboole_0(X0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_23,negated_conjecture,
% 2.97/1.00      ( ~ v1_xboole_0(sK1) ),
% 2.97/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_260,plain,
% 2.97/1.00      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.97/1.00      | r1_tarski(X1,X2)
% 2.97/1.00      | sK1 != X0 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_23]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_261,plain,
% 2.97/1.00      ( ~ r3_orders_2(k2_yellow_1(sK1),X0,X1)
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 2.97/1.00      | r1_tarski(X0,X1) ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_260]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2659,plain,
% 2.97/1.00      ( ~ r3_orders_2(k2_yellow_1(sK1),X0,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 2.97/1.00      | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 2.97/1.00      | r1_tarski(X0,k13_lattice3(k2_yellow_1(sK1),sK2,sK3)) ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_261]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_8330,plain,
% 2.97/1.00      ( ~ r3_orders_2(k2_yellow_1(sK1),sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
% 2.97/1.00      | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 2.97/1.00      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
% 2.97/1.00      | r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3)) ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_2659]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_8327,plain,
% 2.97/1.00      ( ~ r3_orders_2(k2_yellow_1(sK1),sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
% 2.97/1.00      | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 2.97/1.00      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
% 2.97/1.00      | r1_tarski(sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3)) ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_2659]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_21,negated_conjecture,
% 2.97/1.00      ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
% 2.97/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2008,plain,
% 2.97/1.00      ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_16,plain,
% 2.97/1.00      ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
% 2.97/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2018,plain,
% 2.97/1.00      ( m1_subset_1(sK2,sK1) = iProver_top ),
% 2.97/1.00      inference(demodulation,[status(thm)],[c_2008,c_16]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_20,negated_conjecture,
% 2.97/1.00      ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) ),
% 2.97/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2009,plain,
% 2.97/1.00      ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2021,plain,
% 2.97/1.00      ( m1_subset_1(sK3,sK1) = iProver_top ),
% 2.97/1.00      inference(demodulation,[status(thm)],[c_2009,c_16]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_4,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.97/1.00      | ~ v5_orders_2(X1)
% 2.97/1.00      | ~ v1_lattice3(X1)
% 2.97/1.00      | ~ l1_orders_2(X1)
% 2.97/1.00      | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_12,plain,
% 2.97/1.00      ( l1_orders_2(k2_yellow_1(X0)) ),
% 2.97/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_735,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.97/1.00      | ~ v5_orders_2(X1)
% 2.97/1.00      | ~ v1_lattice3(X1)
% 2.97/1.00      | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0)
% 2.97/1.00      | k2_yellow_1(X3) != X1 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_12]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_736,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
% 2.97/1.00      | ~ v5_orders_2(k2_yellow_1(X1))
% 2.97/1.00      | ~ v1_lattice3(k2_yellow_1(X1))
% 2.97/1.00      | k10_lattice3(k2_yellow_1(X1),X0,X2) = k13_lattice3(k2_yellow_1(X1),X0,X2) ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_735]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_13,plain,
% 2.97/1.00      ( v5_orders_2(k2_yellow_1(X0)) ),
% 2.97/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_750,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
% 2.97/1.00      | ~ v1_lattice3(k2_yellow_1(X1))
% 2.97/1.00      | k10_lattice3(k2_yellow_1(X1),X0,X2) = k13_lattice3(k2_yellow_1(X1),X0,X2) ),
% 2.97/1.00      inference(forward_subsumption_resolution,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_736,c_13]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1996,plain,
% 2.97/1.00      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k13_lattice3(k2_yellow_1(X0),X1,X2)
% 2.97/1.00      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 2.97/1.00      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 2.97/1.00      | v1_lattice3(k2_yellow_1(X0)) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_750]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2077,plain,
% 2.97/1.00      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k13_lattice3(k2_yellow_1(X0),X1,X2)
% 2.97/1.00      | m1_subset_1(X2,X0) != iProver_top
% 2.97/1.00      | m1_subset_1(X1,X0) != iProver_top
% 2.97/1.00      | v1_lattice3(k2_yellow_1(X0)) != iProver_top ),
% 2.97/1.00      inference(light_normalisation,[status(thm)],[c_1996,c_16]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_3096,plain,
% 2.97/1.00      ( k10_lattice3(k2_yellow_1(sK1),X0,sK3) = k13_lattice3(k2_yellow_1(sK1),X0,sK3)
% 2.97/1.00      | m1_subset_1(X0,sK1) != iProver_top
% 2.97/1.00      | v1_lattice3(k2_yellow_1(sK1)) != iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_2021,c_2077]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_22,negated_conjecture,
% 2.97/1.00      ( v1_lattice3(k2_yellow_1(sK1)) ),
% 2.97/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_25,plain,
% 2.97/1.00      ( v1_lattice3(k2_yellow_1(sK1)) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_4086,plain,
% 2.97/1.00      ( m1_subset_1(X0,sK1) != iProver_top
% 2.97/1.00      | k10_lattice3(k2_yellow_1(sK1),X0,sK3) = k13_lattice3(k2_yellow_1(sK1),X0,sK3) ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_3096,c_25]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_4087,plain,
% 2.97/1.00      ( k10_lattice3(k2_yellow_1(sK1),X0,sK3) = k13_lattice3(k2_yellow_1(sK1),X0,sK3)
% 2.97/1.00      | m1_subset_1(X0,sK1) != iProver_top ),
% 2.97/1.00      inference(renaming,[status(thm)],[c_4086]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_4094,plain,
% 2.97/1.00      ( k10_lattice3(k2_yellow_1(sK1),sK2,sK3) = k13_lattice3(k2_yellow_1(sK1),sK2,sK3) ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_2018,c_4087]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_0,plain,
% 2.97/1.00      ( ~ r1_tarski(X0,X1)
% 2.97/1.00      | ~ r1_tarski(X2,X1)
% 2.97/1.00      | r1_tarski(k3_tarski(k2_tarski(X2,X0)),X1) ),
% 2.97/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2011,plain,
% 2.97/1.00      ( r1_tarski(X0,X1) != iProver_top
% 2.97/1.00      | r1_tarski(X2,X1) != iProver_top
% 2.97/1.00      | r1_tarski(k3_tarski(k2_tarski(X2,X0)),X1) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_19,negated_conjecture,
% 2.97/1.00      ( ~ r1_tarski(k3_tarski(k2_tarski(sK2,sK3)),k10_lattice3(k2_yellow_1(sK1),sK2,sK3)) ),
% 2.97/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2010,plain,
% 2.97/1.00      ( r1_tarski(k3_tarski(k2_tarski(sK2,sK3)),k10_lattice3(k2_yellow_1(sK1),sK2,sK3)) != iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2912,plain,
% 2.97/1.00      ( r1_tarski(sK3,k10_lattice3(k2_yellow_1(sK1),sK2,sK3)) != iProver_top
% 2.97/1.00      | r1_tarski(sK2,k10_lattice3(k2_yellow_1(sK1),sK2,sK3)) != iProver_top ),
% 2.97/1.00      inference(superposition,[status(thm)],[c_2011,c_2010]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_4504,plain,
% 2.97/1.00      ( r1_tarski(sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3)) != iProver_top
% 2.97/1.00      | r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3)) != iProver_top ),
% 2.97/1.00      inference(demodulation,[status(thm)],[c_4094,c_2912]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_4512,plain,
% 2.97/1.00      ( ~ r1_tarski(sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
% 2.97/1.00      | ~ r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3)) ),
% 2.97/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_4504]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_1,plain,
% 2.97/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 2.97/1.00      | r3_orders_2(X0,X1,X2)
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | v2_struct_0(X0)
% 2.97/1.00      | ~ v3_orders_2(X0)
% 2.97/1.00      | ~ l1_orders_2(X0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_14,plain,
% 2.97/1.00      ( v3_orders_2(k2_yellow_1(X0)) ),
% 2.97/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_342,plain,
% 2.97/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 2.97/1.00      | r3_orders_2(X0,X1,X2)
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.00      | v2_struct_0(X0)
% 2.97/1.00      | ~ l1_orders_2(X0)
% 2.97/1.00      | k2_yellow_1(X3) != X0 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_14]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_343,plain,
% 2.97/1.00      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.97/1.00      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.97/1.00      | v2_struct_0(k2_yellow_1(X0))
% 2.97/1.00      | ~ l1_orders_2(k2_yellow_1(X0)) ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_342]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_347,plain,
% 2.97/1.00      ( v2_struct_0(k2_yellow_1(X0))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.97/1.00      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.97/1.00      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2) ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_343,c_12]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_348,plain,
% 2.97/1.00      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 2.97/1.00      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.97/1.00      | v2_struct_0(k2_yellow_1(X0)) ),
% 2.97/1.00      inference(renaming,[status(thm)],[c_347]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2347,plain,
% 2.97/1.00      ( ~ r1_orders_2(k2_yellow_1(sK1),sK2,X0)
% 2.97/1.00      | r3_orders_2(k2_yellow_1(sK1),sK2,X0)
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 2.97/1.00      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
% 2.97/1.00      | v2_struct_0(k2_yellow_1(sK1)) ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_348]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_3868,plain,
% 2.97/1.00      ( ~ r1_orders_2(k2_yellow_1(sK1),sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
% 2.97/1.00      | r3_orders_2(k2_yellow_1(sK1),sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
% 2.97/1.00      | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 2.97/1.00      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
% 2.97/1.00      | v2_struct_0(k2_yellow_1(sK1)) ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_2347]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2342,plain,
% 2.97/1.00      ( ~ r1_orders_2(k2_yellow_1(sK1),sK3,X0)
% 2.97/1.00      | r3_orders_2(k2_yellow_1(sK1),sK3,X0)
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 2.97/1.00      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
% 2.97/1.00      | v2_struct_0(k2_yellow_1(sK1)) ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_348]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2962,plain,
% 2.97/1.00      ( ~ r1_orders_2(k2_yellow_1(sK1),sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
% 2.97/1.00      | r3_orders_2(k2_yellow_1(sK1),sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
% 2.97/1.00      | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 2.97/1.00      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
% 2.97/1.00      | v2_struct_0(k2_yellow_1(sK1)) ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_2342]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_3,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.97/1.00      | m1_subset_1(k13_lattice3(X1,X2,X0),u1_struct_0(X1))
% 2.97/1.00      | ~ v5_orders_2(X1)
% 2.97/1.00      | ~ v1_lattice3(X1)
% 2.97/1.00      | ~ l1_orders_2(X1) ),
% 2.97/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_758,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.97/1.00      | m1_subset_1(k13_lattice3(X1,X2,X0),u1_struct_0(X1))
% 2.97/1.00      | ~ v5_orders_2(X1)
% 2.97/1.00      | ~ v1_lattice3(X1)
% 2.97/1.00      | k2_yellow_1(X3) != X1 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_12]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_759,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
% 2.97/1.00      | m1_subset_1(k13_lattice3(k2_yellow_1(X1),X0,X2),u1_struct_0(k2_yellow_1(X1)))
% 2.97/1.00      | ~ v5_orders_2(k2_yellow_1(X1))
% 2.97/1.00      | ~ v1_lattice3(k2_yellow_1(X1)) ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_758]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_773,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
% 2.97/1.00      | m1_subset_1(k13_lattice3(k2_yellow_1(X1),X0,X2),u1_struct_0(k2_yellow_1(X1)))
% 2.97/1.00      | ~ v1_lattice3(k2_yellow_1(X1)) ),
% 2.97/1.00      inference(forward_subsumption_resolution,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_759,c_13]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_11,plain,
% 2.97/1.00      ( r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.97/1.00      | ~ v5_orders_2(X0)
% 2.97/1.00      | ~ v1_lattice3(X0)
% 2.97/1.00      | ~ l1_orders_2(X0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_509,plain,
% 2.97/1.00      ( r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
% 2.97/1.00      | ~ v5_orders_2(X0)
% 2.97/1.00      | ~ v1_lattice3(X0)
% 2.97/1.00      | k2_yellow_1(X3) != X0 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_12]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_510,plain,
% 2.97/1.00      ( r1_orders_2(k2_yellow_1(X0),X1,k13_lattice3(k2_yellow_1(X0),X1,X2))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.97/1.00      | ~ m1_subset_1(k13_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
% 2.97/1.00      | ~ v5_orders_2(k2_yellow_1(X0))
% 2.97/1.00      | ~ v1_lattice3(k2_yellow_1(X0)) ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_509]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_514,plain,
% 2.97/1.00      ( ~ m1_subset_1(k13_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.97/1.00      | r1_orders_2(k2_yellow_1(X0),X1,k13_lattice3(k2_yellow_1(X0),X1,X2))
% 2.97/1.00      | ~ v1_lattice3(k2_yellow_1(X0)) ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_510,c_13]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_515,plain,
% 2.97/1.00      ( r1_orders_2(k2_yellow_1(X0),X1,k13_lattice3(k2_yellow_1(X0),X1,X2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.97/1.00      | ~ m1_subset_1(k13_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
% 2.97/1.00      | ~ v1_lattice3(k2_yellow_1(X0)) ),
% 2.97/1.00      inference(renaming,[status(thm)],[c_514]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_778,plain,
% 2.97/1.00      ( r1_orders_2(k2_yellow_1(X0),X1,k13_lattice3(k2_yellow_1(X0),X1,X2))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.97/1.00      | ~ v1_lattice3(k2_yellow_1(X0)) ),
% 2.97/1.00      inference(backward_subsumption_resolution,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_773,c_515]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2323,plain,
% 2.97/1.00      ( r1_orders_2(k2_yellow_1(sK1),sK2,k13_lattice3(k2_yellow_1(sK1),sK2,X0))
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 2.97/1.00      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
% 2.97/1.00      | ~ v1_lattice3(k2_yellow_1(sK1)) ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_778]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2919,plain,
% 2.97/1.00      ( r1_orders_2(k2_yellow_1(sK1),sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
% 2.97/1.00      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
% 2.97/1.00      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
% 2.97/1.00      | ~ v1_lattice3(k2_yellow_1(sK1)) ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_2323]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_10,plain,
% 2.97/1.00      ( r1_orders_2(X0,X1,k13_lattice3(X0,X2,X1))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(k13_lattice3(X0,X2,X1),u1_struct_0(X0))
% 2.97/1.00      | ~ v5_orders_2(X0)
% 2.97/1.00      | ~ v1_lattice3(X0)
% 2.97/1.00      | ~ l1_orders_2(X0) ),
% 2.97/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_536,plain,
% 2.97/1.00      ( r1_orders_2(X0,X1,k13_lattice3(X0,X2,X1))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.00      | ~ m1_subset_1(k13_lattice3(X0,X2,X1),u1_struct_0(X0))
% 2.97/1.00      | ~ v5_orders_2(X0)
% 2.97/1.00      | ~ v1_lattice3(X0)
% 2.97/1.00      | k2_yellow_1(X3) != X0 ),
% 2.97/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_12]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_537,plain,
% 2.97/1.00      ( r1_orders_2(k2_yellow_1(X0),X1,k13_lattice3(k2_yellow_1(X0),X2,X1))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.97/1.00      | ~ m1_subset_1(k13_lattice3(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
% 2.97/1.00      | ~ v5_orders_2(k2_yellow_1(X0))
% 2.97/1.00      | ~ v1_lattice3(k2_yellow_1(X0)) ),
% 2.97/1.00      inference(unflattening,[status(thm)],[c_536]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_539,plain,
% 2.97/1.00      ( ~ m1_subset_1(k13_lattice3(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.97/1.00      | r1_orders_2(k2_yellow_1(X0),X1,k13_lattice3(k2_yellow_1(X0),X2,X1))
% 2.97/1.00      | ~ v1_lattice3(k2_yellow_1(X0)) ),
% 2.97/1.00      inference(global_propositional_subsumption,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_537,c_13]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_540,plain,
% 2.97/1.00      ( r1_orders_2(k2_yellow_1(X0),X1,k13_lattice3(k2_yellow_1(X0),X2,X1))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.97/1.00      | ~ m1_subset_1(k13_lattice3(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
% 2.97/1.00      | ~ v1_lattice3(k2_yellow_1(X0)) ),
% 2.97/1.00      inference(renaming,[status(thm)],[c_539]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_777,plain,
% 2.97/1.00      ( r1_orders_2(k2_yellow_1(X0),X1,k13_lattice3(k2_yellow_1(X0),X2,X1))
% 2.97/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 2.97/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 2.97/1.00      | ~ v1_lattice3(k2_yellow_1(X0)) ),
% 2.97/1.00      inference(backward_subsumption_resolution,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_773,c_540]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2308,plain,
% 2.97/1.00      ( r1_orders_2(k2_yellow_1(sK1),sK3,k13_lattice3(k2_yellow_1(sK1),X0,sK3))
% 2.97/1.00      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 2.97/1.00      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
% 2.97/1.00      | ~ v1_lattice3(k2_yellow_1(sK1)) ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_777]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2763,plain,
% 2.97/1.00      ( r1_orders_2(k2_yellow_1(sK1),sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
% 2.97/1.00      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
% 2.97/1.00      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
% 2.97/1.00      | ~ v1_lattice3(k2_yellow_1(sK1)) ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_2308]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2303,plain,
% 2.97/1.00      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 2.97/1.00      | m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,X0),u1_struct_0(k2_yellow_1(sK1)))
% 2.97/1.00      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
% 2.97/1.00      | ~ v1_lattice3(k2_yellow_1(sK1)) ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_773]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_2436,plain,
% 2.97/1.00      ( m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 2.97/1.00      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
% 2.97/1.00      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
% 2.97/1.00      | ~ v1_lattice3(k2_yellow_1(sK1)) ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_2303]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_15,plain,
% 2.97/1.00      ( v1_xboole_0(X0) | ~ v2_struct_0(k2_yellow_1(X0)) ),
% 2.97/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_37,plain,
% 2.97/1.00      ( v1_xboole_0(sK1) | ~ v2_struct_0(k2_yellow_1(sK1)) ),
% 2.97/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(contradiction,plain,
% 2.97/1.00      ( $false ),
% 2.97/1.00      inference(minisat,
% 2.97/1.00                [status(thm)],
% 2.97/1.00                [c_8330,c_8327,c_4512,c_3868,c_2962,c_2919,c_2763,c_2436,
% 2.97/1.00                 c_37,c_20,c_21,c_22,c_23]) ).
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
% 2.97/1.00  parsing_time:                           0.01
% 2.97/1.00  unif_index_cands_time:                  0.
% 2.97/1.00  unif_index_add_time:                    0.
% 2.97/1.00  orderings_time:                         0.
% 2.97/1.00  out_proof_time:                         0.009
% 2.97/1.00  total_time:                             0.307
% 2.97/1.00  num_of_symbols:                         51
% 2.97/1.00  num_of_terms:                           9612
% 2.97/1.00  
% 2.97/1.00  ------ Preprocessing
% 2.97/1.00  
% 2.97/1.00  num_of_splits:                          0
% 2.97/1.00  num_of_split_atoms:                     0
% 2.97/1.00  num_of_reused_defs:                     0
% 2.97/1.00  num_eq_ax_congr_red:                    24
% 2.97/1.00  num_of_sem_filtered_clauses:            1
% 2.97/1.00  num_of_subtypes:                        0
% 2.97/1.00  monotx_restored_types:                  0
% 2.97/1.00  sat_num_of_epr_types:                   0
% 2.97/1.00  sat_num_of_non_cyclic_types:            0
% 2.97/1.00  sat_guarded_non_collapsed_types:        0
% 2.97/1.00  num_pure_diseq_elim:                    0
% 2.97/1.00  simp_replaced_by:                       0
% 2.97/1.00  res_preprocessed:                       115
% 2.97/1.00  prep_upred:                             0
% 2.97/1.00  prep_unflattend:                        22
% 2.97/1.00  smt_new_axioms:                         0
% 2.97/1.00  pred_elim_cands:                        6
% 2.97/1.00  pred_elim:                              4
% 2.97/1.00  pred_elim_cl:                           4
% 2.97/1.00  pred_elim_cycles:                       10
% 2.97/1.00  merged_defs:                            0
% 2.97/1.00  merged_defs_ncl:                        0
% 2.97/1.00  bin_hyper_res:                          0
% 2.97/1.00  prep_cycles:                            4
% 2.97/1.00  pred_elim_time:                         0.024
% 2.97/1.00  splitting_time:                         0.
% 2.97/1.00  sem_filter_time:                        0.
% 2.97/1.00  monotx_time:                            0.001
% 2.97/1.00  subtype_inf_time:                       0.
% 2.97/1.00  
% 2.97/1.00  ------ Problem properties
% 2.97/1.00  
% 2.97/1.00  clauses:                                20
% 2.97/1.00  conjectures:                            4
% 2.97/1.00  epr:                                    0
% 2.97/1.00  horn:                                   15
% 2.97/1.00  ground:                                 5
% 2.97/1.00  unary:                                  6
% 2.97/1.00  binary:                                 0
% 2.97/1.00  lits:                                   83
% 2.97/1.00  lits_eq:                                6
% 2.97/1.00  fd_pure:                                0
% 2.97/1.00  fd_pseudo:                              0
% 2.97/1.00  fd_cond:                                0
% 2.97/1.00  fd_pseudo_cond:                         4
% 2.97/1.00  ac_symbols:                             0
% 2.97/1.00  
% 2.97/1.00  ------ Propositional Solver
% 2.97/1.00  
% 2.97/1.00  prop_solver_calls:                      28
% 2.97/1.00  prop_fast_solver_calls:                 1380
% 2.97/1.00  smt_solver_calls:                       0
% 2.97/1.00  smt_fast_solver_calls:                  0
% 2.97/1.00  prop_num_of_clauses:                    3818
% 2.97/1.00  prop_preprocess_simplified:             8457
% 2.97/1.00  prop_fo_subsumed:                       16
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
% 2.97/1.00  inst_num_of_clauses:                    1005
% 2.97/1.00  inst_num_in_passive:                    377
% 2.97/1.00  inst_num_in_active:                     265
% 2.97/1.00  inst_num_in_unprocessed:                362
% 2.97/1.00  inst_num_of_loops:                      288
% 2.97/1.00  inst_num_of_learning_restarts:          0
% 2.97/1.00  inst_num_moves_active_passive:          21
% 2.97/1.00  inst_lit_activity:                      0
% 2.97/1.00  inst_lit_activity_moves:                1
% 2.97/1.00  inst_num_tautologies:                   0
% 2.97/1.00  inst_num_prop_implied:                  0
% 2.97/1.00  inst_num_existing_simplified:           0
% 2.97/1.00  inst_num_eq_res_simplified:             0
% 2.97/1.00  inst_num_child_elim:                    0
% 2.97/1.00  inst_num_of_dismatching_blockings:      189
% 2.97/1.00  inst_num_of_non_proper_insts:           540
% 2.97/1.00  inst_num_of_duplicates:                 0
% 2.97/1.00  inst_inst_num_from_inst_to_res:         0
% 2.97/1.00  inst_dismatching_checking_time:         0.
% 2.97/1.00  
% 2.97/1.00  ------ Resolution
% 2.97/1.00  
% 2.97/1.00  res_num_of_clauses:                     0
% 2.97/1.00  res_num_in_passive:                     0
% 2.97/1.00  res_num_in_active:                      0
% 2.97/1.00  res_num_of_loops:                       119
% 2.97/1.00  res_forward_subset_subsumed:            1
% 2.97/1.00  res_backward_subset_subsumed:           0
% 2.97/1.00  res_forward_subsumed:                   0
% 2.97/1.00  res_backward_subsumed:                  0
% 2.97/1.00  res_forward_subsumption_resolution:     2
% 2.97/1.00  res_backward_subsumption_resolution:    2
% 2.97/1.00  res_clause_to_clause_subsumption:       687
% 2.97/1.00  res_orphan_elimination:                 0
% 2.97/1.00  res_tautology_del:                      10
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
% 2.97/1.00  sup_num_of_clauses:                     92
% 2.97/1.00  sup_num_in_active:                      54
% 2.97/1.00  sup_num_in_passive:                     38
% 2.97/1.00  sup_num_of_loops:                       56
% 2.97/1.00  sup_fw_superposition:                   64
% 2.97/1.00  sup_bw_superposition:                   10
% 2.97/1.00  sup_immediate_simplified:               1
% 2.97/1.00  sup_given_eliminated:                   0
% 2.97/1.00  comparisons_done:                       0
% 2.97/1.00  comparisons_avoided:                    0
% 2.97/1.00  
% 2.97/1.00  ------ Simplifications
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  sim_fw_subset_subsumed:                 0
% 2.97/1.00  sim_bw_subset_subsumed:                 0
% 2.97/1.00  sim_fw_subsumed:                        1
% 2.97/1.00  sim_bw_subsumed:                        0
% 2.97/1.00  sim_fw_subsumption_res:                 1
% 2.97/1.00  sim_bw_subsumption_res:                 0
% 2.97/1.00  sim_tautology_del:                      1
% 2.97/1.00  sim_eq_tautology_del:                   0
% 2.97/1.00  sim_eq_res_simp:                        0
% 2.97/1.00  sim_fw_demodulated:                     5
% 2.97/1.00  sim_bw_demodulated:                     2
% 2.97/1.00  sim_light_normalised:                   10
% 2.97/1.00  sim_joinable_taut:                      0
% 2.97/1.00  sim_joinable_simp:                      0
% 2.97/1.00  sim_ac_normalised:                      0
% 2.97/1.00  sim_smt_subsumption:                    0
% 2.97/1.00  
%------------------------------------------------------------------------------
