%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:20:06 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 331 expanded)
%              Number of clauses        :   73 ( 116 expanded)
%              Number of leaves         :   15 (  72 expanded)
%              Depth                    :   17
%              Number of atoms          :  636 (1494 expanded)
%              Number of equality atoms :   61 (  85 expanded)
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

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v1_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v1_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))
          & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
     => ( ~ r1_tarski(k2_xboole_0(X1,sK3),k10_lattice3(k2_yellow_1(X0),X1,sK3))
        & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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

fof(f41,plain,
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

fof(f44,plain,
    ( ~ r1_tarski(k2_xboole_0(sK2,sK3),k10_lattice3(k2_yellow_1(sK1),sK2,sK3))
    & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
    & v1_lattice3(k2_yellow_1(sK1))
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f69,plain,(
    m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f59,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

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

fof(f61,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f67,plain,(
    v1_lattice3(k2_yellow_1(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f70,plain,(
    ~ r1_tarski(k2_xboole_0(sK2,sK3),k10_lattice3(k2_yellow_1(sK1),sK2,sK3)) ),
    inference(cnf_transformation,[],[f44])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

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
    inference(nnf_transformation,[],[f20])).

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

fof(f60,plain,(
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

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
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

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

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
    inference(nnf_transformation,[],[f30])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
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

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | k13_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | k13_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,k13_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f53])).

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

cnf(c_271,plain,
    ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | r1_tarski(X1,X2)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_25])).

cnf(c_272,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK1),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | r1_tarski(X0,X1) ),
    inference(unflattening,[status(thm)],[c_271])).

cnf(c_2714,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK1),X0,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | r1_tarski(X0,k13_lattice3(k2_yellow_1(sK1),sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_272])).

cnf(c_8498,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK1),sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
    | r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2714])).

cnf(c_8495,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK1),sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    | r1_tarski(sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2714])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2128,plain,
    ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_18,plain,
    ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2138,plain,
    ( m1_subset_1(sK2,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2128,c_18])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2129,plain,
    ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2141,plain,
    ( m1_subset_1(sK3,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2129,c_18])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_14,plain,
    ( l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_776,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0)
    | k2_yellow_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_14])).

cnf(c_777,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | ~ v5_orders_2(k2_yellow_1(X1))
    | ~ v1_lattice3(k2_yellow_1(X1))
    | k10_lattice3(k2_yellow_1(X1),X0,X2) = k13_lattice3(k2_yellow_1(X1),X0,X2) ),
    inference(unflattening,[status(thm)],[c_776])).

cnf(c_15,plain,
    ( v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_791,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | ~ v1_lattice3(k2_yellow_1(X1))
    | k10_lattice3(k2_yellow_1(X1),X2,X0) = k13_lattice3(k2_yellow_1(X1),X2,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_777,c_15])).

cnf(c_2116,plain,
    ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k13_lattice3(k2_yellow_1(X0),X1,X2)
    | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | v1_lattice3(k2_yellow_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_791])).

cnf(c_2197,plain,
    ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k13_lattice3(k2_yellow_1(X0),X1,X2)
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | v1_lattice3(k2_yellow_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2116,c_18])).

cnf(c_3229,plain,
    ( k10_lattice3(k2_yellow_1(sK1),X0,sK3) = k13_lattice3(k2_yellow_1(sK1),X0,sK3)
    | m1_subset_1(X0,sK1) != iProver_top
    | v1_lattice3(k2_yellow_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2141,c_2197])).

cnf(c_24,negated_conjecture,
    ( v1_lattice3(k2_yellow_1(sK1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_27,plain,
    ( v1_lattice3(k2_yellow_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3555,plain,
    ( m1_subset_1(X0,sK1) != iProver_top
    | k10_lattice3(k2_yellow_1(sK1),X0,sK3) = k13_lattice3(k2_yellow_1(sK1),X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3229,c_27])).

cnf(c_3556,plain,
    ( k10_lattice3(k2_yellow_1(sK1),X0,sK3) = k13_lattice3(k2_yellow_1(sK1),X0,sK3)
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3555])).

cnf(c_3563,plain,
    ( k10_lattice3(k2_yellow_1(sK1),sK2,sK3) = k13_lattice3(k2_yellow_1(sK1),sK2,sK3) ),
    inference(superposition,[status(thm)],[c_2138,c_3556])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X2,X0),X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2131,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(sK2,sK3),k10_lattice3(k2_yellow_1(sK1),sK2,sK3)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2130,plain,
    ( r1_tarski(k2_xboole_0(sK2,sK3),k10_lattice3(k2_yellow_1(sK1),sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2803,plain,
    ( r1_tarski(sK3,k10_lattice3(k2_yellow_1(sK1),sK2,sK3)) != iProver_top
    | r1_tarski(sK2,k10_lattice3(k2_yellow_1(sK1),sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2131,c_2130])).

cnf(c_4296,plain,
    ( r1_tarski(sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3)) != iProver_top
    | r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3563,c_2803])).

cnf(c_4304,plain,
    ( ~ r1_tarski(sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
    | ~ r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4296])).

cnf(c_3,plain,
    ( ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_16,plain,
    ( v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_344,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_16])).

cnf(c_345,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | v2_struct_0(k2_yellow_1(X0))
    | ~ l1_orders_2(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_344])).

cnf(c_349,plain,
    ( v2_struct_0(k2_yellow_1(X0))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r1_orders_2(k2_yellow_1(X0),X1,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_345,c_14])).

cnf(c_350,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | v2_struct_0(k2_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_349])).

cnf(c_383,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ v1_lattice3(X3)
    | ~ l1_orders_2(X3)
    | k2_yellow_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_350])).

cnf(c_384,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ v1_lattice3(k2_yellow_1(X0))
    | ~ l1_orders_2(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_383])).

cnf(c_388,plain,
    ( ~ v1_lattice3(k2_yellow_1(X0))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r1_orders_2(k2_yellow_1(X0),X1,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_384,c_14])).

cnf(c_389,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ v1_lattice3(k2_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_388])).

cnf(c_2463,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK1),sK2,X0)
    | r3_orders_2(k2_yellow_1(sK1),sK2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
    | ~ v1_lattice3(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_389])).

cnf(c_3217,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK1),sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
    | r3_orders_2(k2_yellow_1(sK1),sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
    | ~ v1_lattice3(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_2463])).

cnf(c_2458,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK1),sK3,X0)
    | r3_orders_2(k2_yellow_1(sK1),sK3,X0)
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    | ~ v1_lattice3(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_389])).

cnf(c_3185,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK1),sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
    | r3_orders_2(k2_yellow_1(sK1),sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    | ~ v1_lattice3(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_2458])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k13_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_799,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k13_lattice3(X1,X2,X0),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | k2_yellow_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_14])).

cnf(c_800,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | m1_subset_1(k13_lattice3(k2_yellow_1(X1),X0,X2),u1_struct_0(k2_yellow_1(X1)))
    | ~ v5_orders_2(k2_yellow_1(X1))
    | ~ v1_lattice3(k2_yellow_1(X1)) ),
    inference(unflattening,[status(thm)],[c_799])).

cnf(c_814,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | m1_subset_1(k13_lattice3(k2_yellow_1(X1),X2,X0),u1_struct_0(k2_yellow_1(X1)))
    | ~ v1_lattice3(k2_yellow_1(X1)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_800,c_15])).

cnf(c_13,plain,
    ( r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_527,plain,
    ( r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_14])).

cnf(c_528,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,k13_lattice3(k2_yellow_1(X0),X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
    | ~ v5_orders_2(k2_yellow_1(X0))
    | ~ v1_lattice3(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_527])).

cnf(c_532,plain,
    ( ~ m1_subset_1(k13_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | r1_orders_2(k2_yellow_1(X0),X1,k13_lattice3(k2_yellow_1(X0),X1,X2))
    | ~ v1_lattice3(k2_yellow_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_528,c_15])).

cnf(c_533,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,k13_lattice3(k2_yellow_1(X0),X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
    | ~ v1_lattice3(k2_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_532])).

cnf(c_819,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,k13_lattice3(k2_yellow_1(X0),X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ v1_lattice3(k2_yellow_1(X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_814,c_533])).

cnf(c_2453,plain,
    ( r1_orders_2(k2_yellow_1(sK1),sK2,k13_lattice3(k2_yellow_1(sK1),sK2,X0))
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
    | ~ v1_lattice3(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_819])).

cnf(c_2789,plain,
    ( r1_orders_2(k2_yellow_1(sK1),sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
    | ~ v1_lattice3(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_2453])).

cnf(c_12,plain,
    ( r1_orders_2(X0,X1,k13_lattice3(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k13_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_554,plain,
    ( r1_orders_2(X0,X1,k13_lattice3(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k13_lattice3(X0,X2,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_14])).

cnf(c_555,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,k13_lattice3(k2_yellow_1(X0),X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
    | ~ v5_orders_2(k2_yellow_1(X0))
    | ~ v1_lattice3(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_554])).

cnf(c_557,plain,
    ( ~ m1_subset_1(k13_lattice3(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | r1_orders_2(k2_yellow_1(X0),X1,k13_lattice3(k2_yellow_1(X0),X2,X1))
    | ~ v1_lattice3(k2_yellow_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_555,c_15])).

cnf(c_558,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,k13_lattice3(k2_yellow_1(X0),X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
    | ~ v1_lattice3(k2_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_557])).

cnf(c_818,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,k13_lattice3(k2_yellow_1(X0),X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ v1_lattice3(k2_yellow_1(X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_814,c_558])).

cnf(c_2438,plain,
    ( r1_orders_2(k2_yellow_1(sK1),sK3,k13_lattice3(k2_yellow_1(sK1),X0,sK3))
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    | ~ v1_lattice3(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_818])).

cnf(c_2758,plain,
    ( r1_orders_2(k2_yellow_1(sK1),sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
    | ~ v1_lattice3(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_2438])).

cnf(c_2428,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
    | m1_subset_1(k13_lattice3(k2_yellow_1(sK1),X0,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    | ~ v1_lattice3(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_814])).

cnf(c_2578,plain,
    ( m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
    | ~ v1_lattice3(k2_yellow_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_2428])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8498,c_8495,c_4304,c_3217,c_3185,c_2789,c_2758,c_2578,c_22,c_23,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:14:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.00/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.01  
% 3.00/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.00/1.01  
% 3.00/1.01  ------  iProver source info
% 3.00/1.01  
% 3.00/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.00/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.00/1.01  git: non_committed_changes: false
% 3.00/1.01  git: last_make_outside_of_git: false
% 3.00/1.01  
% 3.00/1.01  ------ 
% 3.00/1.01  
% 3.00/1.01  ------ Input Options
% 3.00/1.01  
% 3.00/1.01  --out_options                           all
% 3.00/1.01  --tptp_safe_out                         true
% 3.00/1.01  --problem_path                          ""
% 3.00/1.01  --include_path                          ""
% 3.00/1.01  --clausifier                            res/vclausify_rel
% 3.00/1.01  --clausifier_options                    --mode clausify
% 3.00/1.01  --stdin                                 false
% 3.00/1.01  --stats_out                             all
% 3.00/1.01  
% 3.00/1.01  ------ General Options
% 3.00/1.01  
% 3.00/1.01  --fof                                   false
% 3.00/1.01  --time_out_real                         305.
% 3.00/1.01  --time_out_virtual                      -1.
% 3.00/1.01  --symbol_type_check                     false
% 3.00/1.01  --clausify_out                          false
% 3.00/1.01  --sig_cnt_out                           false
% 3.00/1.01  --trig_cnt_out                          false
% 3.00/1.01  --trig_cnt_out_tolerance                1.
% 3.00/1.01  --trig_cnt_out_sk_spl                   false
% 3.00/1.01  --abstr_cl_out                          false
% 3.00/1.01  
% 3.00/1.01  ------ Global Options
% 3.00/1.01  
% 3.00/1.01  --schedule                              default
% 3.00/1.01  --add_important_lit                     false
% 3.00/1.01  --prop_solver_per_cl                    1000
% 3.00/1.01  --min_unsat_core                        false
% 3.00/1.01  --soft_assumptions                      false
% 3.00/1.01  --soft_lemma_size                       3
% 3.00/1.01  --prop_impl_unit_size                   0
% 3.00/1.01  --prop_impl_unit                        []
% 3.00/1.01  --share_sel_clauses                     true
% 3.00/1.01  --reset_solvers                         false
% 3.00/1.01  --bc_imp_inh                            [conj_cone]
% 3.00/1.01  --conj_cone_tolerance                   3.
% 3.00/1.01  --extra_neg_conj                        none
% 3.00/1.01  --large_theory_mode                     true
% 3.00/1.01  --prolific_symb_bound                   200
% 3.00/1.01  --lt_threshold                          2000
% 3.00/1.01  --clause_weak_htbl                      true
% 3.00/1.01  --gc_record_bc_elim                     false
% 3.00/1.01  
% 3.00/1.01  ------ Preprocessing Options
% 3.00/1.01  
% 3.00/1.01  --preprocessing_flag                    true
% 3.00/1.01  --time_out_prep_mult                    0.1
% 3.00/1.01  --splitting_mode                        input
% 3.00/1.01  --splitting_grd                         true
% 3.00/1.01  --splitting_cvd                         false
% 3.00/1.01  --splitting_cvd_svl                     false
% 3.00/1.01  --splitting_nvd                         32
% 3.00/1.01  --sub_typing                            true
% 3.00/1.01  --prep_gs_sim                           true
% 3.00/1.01  --prep_unflatten                        true
% 3.00/1.01  --prep_res_sim                          true
% 3.00/1.01  --prep_upred                            true
% 3.00/1.01  --prep_sem_filter                       exhaustive
% 3.00/1.01  --prep_sem_filter_out                   false
% 3.00/1.01  --pred_elim                             true
% 3.00/1.01  --res_sim_input                         true
% 3.00/1.01  --eq_ax_congr_red                       true
% 3.00/1.01  --pure_diseq_elim                       true
% 3.00/1.01  --brand_transform                       false
% 3.00/1.01  --non_eq_to_eq                          false
% 3.00/1.01  --prep_def_merge                        true
% 3.00/1.01  --prep_def_merge_prop_impl              false
% 3.00/1.01  --prep_def_merge_mbd                    true
% 3.00/1.01  --prep_def_merge_tr_red                 false
% 3.00/1.01  --prep_def_merge_tr_cl                  false
% 3.00/1.01  --smt_preprocessing                     true
% 3.00/1.01  --smt_ac_axioms                         fast
% 3.00/1.01  --preprocessed_out                      false
% 3.00/1.01  --preprocessed_stats                    false
% 3.00/1.01  
% 3.00/1.01  ------ Abstraction refinement Options
% 3.00/1.01  
% 3.00/1.01  --abstr_ref                             []
% 3.00/1.01  --abstr_ref_prep                        false
% 3.00/1.01  --abstr_ref_until_sat                   false
% 3.00/1.01  --abstr_ref_sig_restrict                funpre
% 3.00/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/1.01  --abstr_ref_under                       []
% 3.00/1.01  
% 3.00/1.01  ------ SAT Options
% 3.00/1.01  
% 3.00/1.01  --sat_mode                              false
% 3.00/1.01  --sat_fm_restart_options                ""
% 3.00/1.01  --sat_gr_def                            false
% 3.00/1.01  --sat_epr_types                         true
% 3.00/1.01  --sat_non_cyclic_types                  false
% 3.00/1.01  --sat_finite_models                     false
% 3.00/1.01  --sat_fm_lemmas                         false
% 3.00/1.01  --sat_fm_prep                           false
% 3.00/1.01  --sat_fm_uc_incr                        true
% 3.00/1.01  --sat_out_model                         small
% 3.00/1.01  --sat_out_clauses                       false
% 3.00/1.01  
% 3.00/1.01  ------ QBF Options
% 3.00/1.01  
% 3.00/1.01  --qbf_mode                              false
% 3.00/1.01  --qbf_elim_univ                         false
% 3.00/1.01  --qbf_dom_inst                          none
% 3.00/1.01  --qbf_dom_pre_inst                      false
% 3.00/1.01  --qbf_sk_in                             false
% 3.00/1.01  --qbf_pred_elim                         true
% 3.00/1.01  --qbf_split                             512
% 3.00/1.01  
% 3.00/1.01  ------ BMC1 Options
% 3.00/1.01  
% 3.00/1.01  --bmc1_incremental                      false
% 3.00/1.01  --bmc1_axioms                           reachable_all
% 3.00/1.01  --bmc1_min_bound                        0
% 3.00/1.01  --bmc1_max_bound                        -1
% 3.00/1.01  --bmc1_max_bound_default                -1
% 3.00/1.01  --bmc1_symbol_reachability              true
% 3.00/1.01  --bmc1_property_lemmas                  false
% 3.00/1.01  --bmc1_k_induction                      false
% 3.00/1.01  --bmc1_non_equiv_states                 false
% 3.00/1.01  --bmc1_deadlock                         false
% 3.00/1.01  --bmc1_ucm                              false
% 3.00/1.01  --bmc1_add_unsat_core                   none
% 3.00/1.01  --bmc1_unsat_core_children              false
% 3.00/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/1.01  --bmc1_out_stat                         full
% 3.00/1.01  --bmc1_ground_init                      false
% 3.00/1.01  --bmc1_pre_inst_next_state              false
% 3.00/1.01  --bmc1_pre_inst_state                   false
% 3.00/1.01  --bmc1_pre_inst_reach_state             false
% 3.00/1.01  --bmc1_out_unsat_core                   false
% 3.00/1.01  --bmc1_aig_witness_out                  false
% 3.00/1.01  --bmc1_verbose                          false
% 3.00/1.01  --bmc1_dump_clauses_tptp                false
% 3.00/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.00/1.01  --bmc1_dump_file                        -
% 3.00/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.00/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.00/1.01  --bmc1_ucm_extend_mode                  1
% 3.00/1.01  --bmc1_ucm_init_mode                    2
% 3.00/1.01  --bmc1_ucm_cone_mode                    none
% 3.00/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.00/1.01  --bmc1_ucm_relax_model                  4
% 3.00/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.00/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/1.01  --bmc1_ucm_layered_model                none
% 3.00/1.01  --bmc1_ucm_max_lemma_size               10
% 3.00/1.01  
% 3.00/1.01  ------ AIG Options
% 3.00/1.01  
% 3.00/1.01  --aig_mode                              false
% 3.00/1.01  
% 3.00/1.01  ------ Instantiation Options
% 3.00/1.01  
% 3.00/1.01  --instantiation_flag                    true
% 3.00/1.01  --inst_sos_flag                         false
% 3.00/1.01  --inst_sos_phase                        true
% 3.00/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/1.01  --inst_lit_sel_side                     num_symb
% 3.00/1.01  --inst_solver_per_active                1400
% 3.00/1.01  --inst_solver_calls_frac                1.
% 3.00/1.01  --inst_passive_queue_type               priority_queues
% 3.00/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/1.01  --inst_passive_queues_freq              [25;2]
% 3.00/1.01  --inst_dismatching                      true
% 3.00/1.01  --inst_eager_unprocessed_to_passive     true
% 3.00/1.01  --inst_prop_sim_given                   true
% 3.00/1.01  --inst_prop_sim_new                     false
% 3.00/1.01  --inst_subs_new                         false
% 3.00/1.01  --inst_eq_res_simp                      false
% 3.00/1.01  --inst_subs_given                       false
% 3.00/1.01  --inst_orphan_elimination               true
% 3.00/1.01  --inst_learning_loop_flag               true
% 3.00/1.01  --inst_learning_start                   3000
% 3.00/1.01  --inst_learning_factor                  2
% 3.00/1.01  --inst_start_prop_sim_after_learn       3
% 3.00/1.01  --inst_sel_renew                        solver
% 3.00/1.01  --inst_lit_activity_flag                true
% 3.00/1.01  --inst_restr_to_given                   false
% 3.00/1.01  --inst_activity_threshold               500
% 3.00/1.01  --inst_out_proof                        true
% 3.00/1.01  
% 3.00/1.01  ------ Resolution Options
% 3.00/1.01  
% 3.00/1.01  --resolution_flag                       true
% 3.00/1.01  --res_lit_sel                           adaptive
% 3.00/1.01  --res_lit_sel_side                      none
% 3.00/1.01  --res_ordering                          kbo
% 3.00/1.01  --res_to_prop_solver                    active
% 3.00/1.01  --res_prop_simpl_new                    false
% 3.00/1.01  --res_prop_simpl_given                  true
% 3.00/1.01  --res_passive_queue_type                priority_queues
% 3.00/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/1.01  --res_passive_queues_freq               [15;5]
% 3.00/1.01  --res_forward_subs                      full
% 3.00/1.01  --res_backward_subs                     full
% 3.00/1.01  --res_forward_subs_resolution           true
% 3.00/1.01  --res_backward_subs_resolution          true
% 3.00/1.01  --res_orphan_elimination                true
% 3.00/1.01  --res_time_limit                        2.
% 3.00/1.01  --res_out_proof                         true
% 3.00/1.01  
% 3.00/1.01  ------ Superposition Options
% 3.00/1.01  
% 3.00/1.01  --superposition_flag                    true
% 3.00/1.01  --sup_passive_queue_type                priority_queues
% 3.00/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.00/1.01  --demod_completeness_check              fast
% 3.00/1.01  --demod_use_ground                      true
% 3.00/1.01  --sup_to_prop_solver                    passive
% 3.00/1.01  --sup_prop_simpl_new                    true
% 3.00/1.01  --sup_prop_simpl_given                  true
% 3.00/1.01  --sup_fun_splitting                     false
% 3.00/1.01  --sup_smt_interval                      50000
% 3.00/1.01  
% 3.00/1.01  ------ Superposition Simplification Setup
% 3.00/1.01  
% 3.00/1.01  --sup_indices_passive                   []
% 3.00/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.01  --sup_full_bw                           [BwDemod]
% 3.00/1.01  --sup_immed_triv                        [TrivRules]
% 3.00/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.01  --sup_immed_bw_main                     []
% 3.00/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.01  
% 3.00/1.01  ------ Combination Options
% 3.00/1.01  
% 3.00/1.01  --comb_res_mult                         3
% 3.00/1.01  --comb_sup_mult                         2
% 3.00/1.01  --comb_inst_mult                        10
% 3.00/1.01  
% 3.00/1.01  ------ Debug Options
% 3.00/1.01  
% 3.00/1.01  --dbg_backtrace                         false
% 3.00/1.01  --dbg_dump_prop_clauses                 false
% 3.00/1.01  --dbg_dump_prop_clauses_file            -
% 3.00/1.01  --dbg_out_stat                          false
% 3.00/1.01  ------ Parsing...
% 3.00/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.00/1.01  
% 3.00/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.00/1.01  
% 3.00/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.00/1.01  
% 3.00/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.00/1.01  ------ Proving...
% 3.00/1.01  ------ Problem Properties 
% 3.00/1.01  
% 3.00/1.01  
% 3.00/1.01  clauses                                 21
% 3.00/1.01  conjectures                             4
% 3.00/1.01  EPR                                     0
% 3.00/1.01  Horn                                    18
% 3.00/1.01  unary                                   6
% 3.00/1.01  binary                                  0
% 3.00/1.01  lits                                    87
% 3.00/1.01  lits eq                                 8
% 3.00/1.01  fd_pure                                 0
% 3.00/1.01  fd_pseudo                               0
% 3.00/1.01  fd_cond                                 0
% 3.00/1.01  fd_pseudo_cond                          4
% 3.00/1.01  AC symbols                              0
% 3.00/1.01  
% 3.00/1.01  ------ Schedule dynamic 5 is on 
% 3.00/1.01  
% 3.00/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.00/1.01  
% 3.00/1.01  
% 3.00/1.01  ------ 
% 3.00/1.01  Current options:
% 3.00/1.01  ------ 
% 3.00/1.01  
% 3.00/1.01  ------ Input Options
% 3.00/1.01  
% 3.00/1.01  --out_options                           all
% 3.00/1.01  --tptp_safe_out                         true
% 3.00/1.01  --problem_path                          ""
% 3.00/1.01  --include_path                          ""
% 3.00/1.01  --clausifier                            res/vclausify_rel
% 3.00/1.01  --clausifier_options                    --mode clausify
% 3.00/1.01  --stdin                                 false
% 3.00/1.01  --stats_out                             all
% 3.00/1.01  
% 3.00/1.01  ------ General Options
% 3.00/1.01  
% 3.00/1.01  --fof                                   false
% 3.00/1.01  --time_out_real                         305.
% 3.00/1.01  --time_out_virtual                      -1.
% 3.00/1.01  --symbol_type_check                     false
% 3.00/1.01  --clausify_out                          false
% 3.00/1.01  --sig_cnt_out                           false
% 3.00/1.01  --trig_cnt_out                          false
% 3.00/1.01  --trig_cnt_out_tolerance                1.
% 3.00/1.01  --trig_cnt_out_sk_spl                   false
% 3.00/1.01  --abstr_cl_out                          false
% 3.00/1.01  
% 3.00/1.01  ------ Global Options
% 3.00/1.01  
% 3.00/1.01  --schedule                              default
% 3.00/1.01  --add_important_lit                     false
% 3.00/1.01  --prop_solver_per_cl                    1000
% 3.00/1.01  --min_unsat_core                        false
% 3.00/1.01  --soft_assumptions                      false
% 3.00/1.01  --soft_lemma_size                       3
% 3.00/1.01  --prop_impl_unit_size                   0
% 3.00/1.01  --prop_impl_unit                        []
% 3.00/1.01  --share_sel_clauses                     true
% 3.00/1.01  --reset_solvers                         false
% 3.00/1.01  --bc_imp_inh                            [conj_cone]
% 3.00/1.01  --conj_cone_tolerance                   3.
% 3.00/1.01  --extra_neg_conj                        none
% 3.00/1.01  --large_theory_mode                     true
% 3.00/1.01  --prolific_symb_bound                   200
% 3.00/1.01  --lt_threshold                          2000
% 3.00/1.01  --clause_weak_htbl                      true
% 3.00/1.01  --gc_record_bc_elim                     false
% 3.00/1.01  
% 3.00/1.01  ------ Preprocessing Options
% 3.00/1.01  
% 3.00/1.01  --preprocessing_flag                    true
% 3.00/1.01  --time_out_prep_mult                    0.1
% 3.00/1.01  --splitting_mode                        input
% 3.00/1.01  --splitting_grd                         true
% 3.00/1.01  --splitting_cvd                         false
% 3.00/1.01  --splitting_cvd_svl                     false
% 3.00/1.01  --splitting_nvd                         32
% 3.00/1.01  --sub_typing                            true
% 3.00/1.01  --prep_gs_sim                           true
% 3.00/1.01  --prep_unflatten                        true
% 3.00/1.01  --prep_res_sim                          true
% 3.00/1.01  --prep_upred                            true
% 3.00/1.01  --prep_sem_filter                       exhaustive
% 3.00/1.01  --prep_sem_filter_out                   false
% 3.00/1.01  --pred_elim                             true
% 3.00/1.01  --res_sim_input                         true
% 3.00/1.01  --eq_ax_congr_red                       true
% 3.00/1.01  --pure_diseq_elim                       true
% 3.00/1.01  --brand_transform                       false
% 3.00/1.01  --non_eq_to_eq                          false
% 3.00/1.01  --prep_def_merge                        true
% 3.00/1.01  --prep_def_merge_prop_impl              false
% 3.00/1.01  --prep_def_merge_mbd                    true
% 3.00/1.01  --prep_def_merge_tr_red                 false
% 3.00/1.01  --prep_def_merge_tr_cl                  false
% 3.00/1.01  --smt_preprocessing                     true
% 3.00/1.01  --smt_ac_axioms                         fast
% 3.00/1.01  --preprocessed_out                      false
% 3.00/1.01  --preprocessed_stats                    false
% 3.00/1.01  
% 3.00/1.01  ------ Abstraction refinement Options
% 3.00/1.01  
% 3.00/1.01  --abstr_ref                             []
% 3.00/1.01  --abstr_ref_prep                        false
% 3.00/1.01  --abstr_ref_until_sat                   false
% 3.00/1.01  --abstr_ref_sig_restrict                funpre
% 3.00/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/1.01  --abstr_ref_under                       []
% 3.00/1.01  
% 3.00/1.01  ------ SAT Options
% 3.00/1.01  
% 3.00/1.01  --sat_mode                              false
% 3.00/1.01  --sat_fm_restart_options                ""
% 3.00/1.01  --sat_gr_def                            false
% 3.00/1.01  --sat_epr_types                         true
% 3.00/1.01  --sat_non_cyclic_types                  false
% 3.00/1.01  --sat_finite_models                     false
% 3.00/1.01  --sat_fm_lemmas                         false
% 3.00/1.01  --sat_fm_prep                           false
% 3.00/1.01  --sat_fm_uc_incr                        true
% 3.00/1.01  --sat_out_model                         small
% 3.00/1.01  --sat_out_clauses                       false
% 3.00/1.01  
% 3.00/1.01  ------ QBF Options
% 3.00/1.01  
% 3.00/1.01  --qbf_mode                              false
% 3.00/1.01  --qbf_elim_univ                         false
% 3.00/1.01  --qbf_dom_inst                          none
% 3.00/1.01  --qbf_dom_pre_inst                      false
% 3.00/1.01  --qbf_sk_in                             false
% 3.00/1.01  --qbf_pred_elim                         true
% 3.00/1.01  --qbf_split                             512
% 3.00/1.01  
% 3.00/1.01  ------ BMC1 Options
% 3.00/1.01  
% 3.00/1.01  --bmc1_incremental                      false
% 3.00/1.01  --bmc1_axioms                           reachable_all
% 3.00/1.01  --bmc1_min_bound                        0
% 3.00/1.01  --bmc1_max_bound                        -1
% 3.00/1.01  --bmc1_max_bound_default                -1
% 3.00/1.01  --bmc1_symbol_reachability              true
% 3.00/1.01  --bmc1_property_lemmas                  false
% 3.00/1.01  --bmc1_k_induction                      false
% 3.00/1.01  --bmc1_non_equiv_states                 false
% 3.00/1.01  --bmc1_deadlock                         false
% 3.00/1.01  --bmc1_ucm                              false
% 3.00/1.01  --bmc1_add_unsat_core                   none
% 3.00/1.01  --bmc1_unsat_core_children              false
% 3.00/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/1.01  --bmc1_out_stat                         full
% 3.00/1.01  --bmc1_ground_init                      false
% 3.00/1.01  --bmc1_pre_inst_next_state              false
% 3.00/1.01  --bmc1_pre_inst_state                   false
% 3.00/1.01  --bmc1_pre_inst_reach_state             false
% 3.00/1.01  --bmc1_out_unsat_core                   false
% 3.00/1.01  --bmc1_aig_witness_out                  false
% 3.00/1.01  --bmc1_verbose                          false
% 3.00/1.01  --bmc1_dump_clauses_tptp                false
% 3.00/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.00/1.01  --bmc1_dump_file                        -
% 3.00/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.00/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.00/1.01  --bmc1_ucm_extend_mode                  1
% 3.00/1.01  --bmc1_ucm_init_mode                    2
% 3.00/1.01  --bmc1_ucm_cone_mode                    none
% 3.00/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.00/1.01  --bmc1_ucm_relax_model                  4
% 3.00/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.00/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/1.01  --bmc1_ucm_layered_model                none
% 3.00/1.01  --bmc1_ucm_max_lemma_size               10
% 3.00/1.01  
% 3.00/1.01  ------ AIG Options
% 3.00/1.01  
% 3.00/1.01  --aig_mode                              false
% 3.00/1.01  
% 3.00/1.01  ------ Instantiation Options
% 3.00/1.01  
% 3.00/1.01  --instantiation_flag                    true
% 3.00/1.01  --inst_sos_flag                         false
% 3.00/1.01  --inst_sos_phase                        true
% 3.00/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/1.01  --inst_lit_sel_side                     none
% 3.00/1.01  --inst_solver_per_active                1400
% 3.00/1.01  --inst_solver_calls_frac                1.
% 3.00/1.01  --inst_passive_queue_type               priority_queues
% 3.00/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/1.01  --inst_passive_queues_freq              [25;2]
% 3.00/1.01  --inst_dismatching                      true
% 3.00/1.01  --inst_eager_unprocessed_to_passive     true
% 3.00/1.01  --inst_prop_sim_given                   true
% 3.00/1.01  --inst_prop_sim_new                     false
% 3.00/1.01  --inst_subs_new                         false
% 3.00/1.01  --inst_eq_res_simp                      false
% 3.00/1.01  --inst_subs_given                       false
% 3.00/1.01  --inst_orphan_elimination               true
% 3.00/1.01  --inst_learning_loop_flag               true
% 3.00/1.01  --inst_learning_start                   3000
% 3.00/1.01  --inst_learning_factor                  2
% 3.00/1.01  --inst_start_prop_sim_after_learn       3
% 3.00/1.01  --inst_sel_renew                        solver
% 3.00/1.01  --inst_lit_activity_flag                true
% 3.00/1.01  --inst_restr_to_given                   false
% 3.00/1.01  --inst_activity_threshold               500
% 3.00/1.01  --inst_out_proof                        true
% 3.00/1.01  
% 3.00/1.01  ------ Resolution Options
% 3.00/1.01  
% 3.00/1.01  --resolution_flag                       false
% 3.00/1.01  --res_lit_sel                           adaptive
% 3.00/1.01  --res_lit_sel_side                      none
% 3.00/1.01  --res_ordering                          kbo
% 3.00/1.01  --res_to_prop_solver                    active
% 3.00/1.01  --res_prop_simpl_new                    false
% 3.00/1.01  --res_prop_simpl_given                  true
% 3.00/1.01  --res_passive_queue_type                priority_queues
% 3.00/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/1.01  --res_passive_queues_freq               [15;5]
% 3.00/1.01  --res_forward_subs                      full
% 3.00/1.01  --res_backward_subs                     full
% 3.00/1.01  --res_forward_subs_resolution           true
% 3.00/1.01  --res_backward_subs_resolution          true
% 3.00/1.01  --res_orphan_elimination                true
% 3.00/1.01  --res_time_limit                        2.
% 3.00/1.01  --res_out_proof                         true
% 3.00/1.01  
% 3.00/1.01  ------ Superposition Options
% 3.00/1.01  
% 3.00/1.01  --superposition_flag                    true
% 3.00/1.01  --sup_passive_queue_type                priority_queues
% 3.00/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.00/1.01  --demod_completeness_check              fast
% 3.00/1.01  --demod_use_ground                      true
% 3.00/1.01  --sup_to_prop_solver                    passive
% 3.00/1.01  --sup_prop_simpl_new                    true
% 3.00/1.01  --sup_prop_simpl_given                  true
% 3.00/1.01  --sup_fun_splitting                     false
% 3.00/1.01  --sup_smt_interval                      50000
% 3.00/1.01  
% 3.00/1.01  ------ Superposition Simplification Setup
% 3.00/1.01  
% 3.00/1.01  --sup_indices_passive                   []
% 3.00/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.01  --sup_full_bw                           [BwDemod]
% 3.00/1.01  --sup_immed_triv                        [TrivRules]
% 3.00/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.01  --sup_immed_bw_main                     []
% 3.00/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.01  
% 3.00/1.01  ------ Combination Options
% 3.00/1.01  
% 3.00/1.01  --comb_res_mult                         3
% 3.00/1.01  --comb_sup_mult                         2
% 3.00/1.01  --comb_inst_mult                        10
% 3.00/1.01  
% 3.00/1.01  ------ Debug Options
% 3.00/1.01  
% 3.00/1.01  --dbg_backtrace                         false
% 3.00/1.01  --dbg_dump_prop_clauses                 false
% 3.00/1.01  --dbg_dump_prop_clauses_file            -
% 3.00/1.01  --dbg_out_stat                          false
% 3.00/1.01  
% 3.00/1.01  
% 3.00/1.01  
% 3.00/1.01  
% 3.00/1.01  ------ Proving...
% 3.00/1.01  
% 3.00/1.01  
% 3.00/1.01  % SZS status Theorem for theBenchmark.p
% 3.00/1.01  
% 3.00/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.00/1.01  
% 3.00/1.01  fof(f11,axiom,(
% 3.00/1.01    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 3.00/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f31,plain,(
% 3.00/1.01    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 3.00/1.01    inference(ennf_transformation,[],[f11])).
% 3.00/1.01  
% 3.00/1.01  fof(f40,plain,(
% 3.00/1.01    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 3.00/1.01    inference(nnf_transformation,[],[f31])).
% 3.00/1.01  
% 3.00/1.01  fof(f64,plain,(
% 3.00/1.01    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 3.00/1.01    inference(cnf_transformation,[],[f40])).
% 3.00/1.01  
% 3.00/1.01  fof(f12,conjecture,(
% 3.00/1.01    ! [X0] : (~v1_xboole_0(X0) => (v1_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))))))),
% 3.00/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f13,negated_conjecture,(
% 3.00/1.01    ~! [X0] : (~v1_xboole_0(X0) => (v1_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))))))),
% 3.00/1.01    inference(negated_conjecture,[],[f12])).
% 3.00/1.01  
% 3.00/1.01  fof(f32,plain,(
% 3.00/1.01    ? [X0] : ((? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v1_lattice3(k2_yellow_1(X0))) & ~v1_xboole_0(X0))),
% 3.00/1.01    inference(ennf_transformation,[],[f13])).
% 3.00/1.01  
% 3.00/1.01  fof(f33,plain,(
% 3.00/1.01    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v1_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0))),
% 3.00/1.01    inference(flattening,[],[f32])).
% 3.00/1.01  
% 3.00/1.01  fof(f43,plain,(
% 3.00/1.01    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) => (~r1_tarski(k2_xboole_0(X1,sK3),k10_lattice3(k2_yellow_1(X0),X1,sK3)) & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0))))) )),
% 3.00/1.01    introduced(choice_axiom,[])).
% 3.00/1.01  
% 3.00/1.01  fof(f42,plain,(
% 3.00/1.01    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) => (? [X2] : (~r1_tarski(k2_xboole_0(sK2,X2),k10_lattice3(k2_yellow_1(X0),sK2,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(X0))))) )),
% 3.00/1.01    introduced(choice_axiom,[])).
% 3.00/1.01  
% 3.00/1.01  fof(f41,plain,(
% 3.00/1.01    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v1_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(sK1),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK1)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))) & v1_lattice3(k2_yellow_1(sK1)) & ~v1_xboole_0(sK1))),
% 3.00/1.01    introduced(choice_axiom,[])).
% 3.00/1.01  
% 3.00/1.01  fof(f44,plain,(
% 3.00/1.01    ((~r1_tarski(k2_xboole_0(sK2,sK3),k10_lattice3(k2_yellow_1(sK1),sK2,sK3)) & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))) & v1_lattice3(k2_yellow_1(sK1)) & ~v1_xboole_0(sK1)),
% 3.00/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f43,f42,f41])).
% 3.00/1.01  
% 3.00/1.01  fof(f66,plain,(
% 3.00/1.01    ~v1_xboole_0(sK1)),
% 3.00/1.01    inference(cnf_transformation,[],[f44])).
% 3.00/1.01  
% 3.00/1.01  fof(f68,plain,(
% 3.00/1.01    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))),
% 3.00/1.01    inference(cnf_transformation,[],[f44])).
% 3.00/1.01  
% 3.00/1.01  fof(f10,axiom,(
% 3.00/1.01    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 3.00/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f62,plain,(
% 3.00/1.01    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 3.00/1.01    inference(cnf_transformation,[],[f10])).
% 3.00/1.01  
% 3.00/1.01  fof(f69,plain,(
% 3.00/1.01    m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))),
% 3.00/1.01    inference(cnf_transformation,[],[f44])).
% 3.00/1.01  
% 3.00/1.01  fof(f5,axiom,(
% 3.00/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2))),
% 3.00/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f25,plain,(
% 3.00/1.01    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 3.00/1.01    inference(ennf_transformation,[],[f5])).
% 3.00/1.01  
% 3.00/1.01  fof(f26,plain,(
% 3.00/1.01    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 3.00/1.01    inference(flattening,[],[f25])).
% 3.00/1.01  
% 3.00/1.01  fof(f50,plain,(
% 3.00/1.01    ( ! [X2,X0,X1] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 3.00/1.01    inference(cnf_transformation,[],[f26])).
% 3.00/1.01  
% 3.00/1.01  fof(f8,axiom,(
% 3.00/1.01    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 3.00/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f16,plain,(
% 3.00/1.01    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 3.00/1.01    inference(pure_predicate_removal,[],[f8])).
% 3.00/1.01  
% 3.00/1.01  fof(f59,plain,(
% 3.00/1.01    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 3.00/1.01    inference(cnf_transformation,[],[f16])).
% 3.00/1.01  
% 3.00/1.01  fof(f9,axiom,(
% 3.00/1.01    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 3.00/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f14,plain,(
% 3.00/1.01    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 3.00/1.01    inference(pure_predicate_removal,[],[f9])).
% 3.00/1.01  
% 3.00/1.01  fof(f15,plain,(
% 3.00/1.01    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 3.00/1.01    inference(pure_predicate_removal,[],[f14])).
% 3.00/1.01  
% 3.00/1.01  fof(f61,plain,(
% 3.00/1.01    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 3.00/1.01    inference(cnf_transformation,[],[f15])).
% 3.00/1.01  
% 3.00/1.01  fof(f67,plain,(
% 3.00/1.01    v1_lattice3(k2_yellow_1(sK1))),
% 3.00/1.01    inference(cnf_transformation,[],[f44])).
% 3.00/1.01  
% 3.00/1.01  fof(f1,axiom,(
% 3.00/1.01    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 3.00/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f17,plain,(
% 3.00/1.01    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 3.00/1.01    inference(ennf_transformation,[],[f1])).
% 3.00/1.01  
% 3.00/1.01  fof(f18,plain,(
% 3.00/1.01    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 3.00/1.01    inference(flattening,[],[f17])).
% 3.00/1.01  
% 3.00/1.01  fof(f45,plain,(
% 3.00/1.01    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.00/1.01    inference(cnf_transformation,[],[f18])).
% 3.00/1.01  
% 3.00/1.01  fof(f70,plain,(
% 3.00/1.01    ~r1_tarski(k2_xboole_0(sK2,sK3),k10_lattice3(k2_yellow_1(sK1),sK2,sK3))),
% 3.00/1.01    inference(cnf_transformation,[],[f44])).
% 3.00/1.01  
% 3.00/1.01  fof(f3,axiom,(
% 3.00/1.01    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 3.00/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f21,plain,(
% 3.00/1.01    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 3.00/1.01    inference(ennf_transformation,[],[f3])).
% 3.00/1.01  
% 3.00/1.01  fof(f22,plain,(
% 3.00/1.01    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 3.00/1.01    inference(flattening,[],[f21])).
% 3.00/1.01  
% 3.00/1.01  fof(f48,plain,(
% 3.00/1.01    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 3.00/1.01    inference(cnf_transformation,[],[f22])).
% 3.00/1.01  
% 3.00/1.01  fof(f2,axiom,(
% 3.00/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 3.00/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f19,plain,(
% 3.00/1.01    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.00/1.01    inference(ennf_transformation,[],[f2])).
% 3.00/1.01  
% 3.00/1.01  fof(f20,plain,(
% 3.00/1.01    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.00/1.01    inference(flattening,[],[f19])).
% 3.00/1.01  
% 3.00/1.01  fof(f34,plain,(
% 3.00/1.01    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.00/1.01    inference(nnf_transformation,[],[f20])).
% 3.00/1.01  
% 3.00/1.01  fof(f47,plain,(
% 3.00/1.01    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.00/1.01    inference(cnf_transformation,[],[f34])).
% 3.00/1.01  
% 3.00/1.01  fof(f60,plain,(
% 3.00/1.01    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 3.00/1.01    inference(cnf_transformation,[],[f15])).
% 3.00/1.01  
% 3.00/1.01  fof(f4,axiom,(
% 3.00/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 3.00/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f23,plain,(
% 3.00/1.01    ! [X0,X1,X2] : (m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 3.00/1.01    inference(ennf_transformation,[],[f4])).
% 3.00/1.01  
% 3.00/1.01  fof(f24,plain,(
% 3.00/1.01    ! [X0,X1,X2] : (m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 3.00/1.01    inference(flattening,[],[f23])).
% 3.00/1.01  
% 3.00/1.01  fof(f49,plain,(
% 3.00/1.01    ( ! [X2,X0,X1] : (m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 3.00/1.01    inference(cnf_transformation,[],[f24])).
% 3.00/1.01  
% 3.00/1.01  fof(f7,axiom,(
% 3.00/1.01    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k13_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 3.00/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f29,plain,(
% 3.00/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k13_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 3.00/1.01    inference(ennf_transformation,[],[f7])).
% 3.00/1.01  
% 3.00/1.01  fof(f30,plain,(
% 3.00/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k13_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 3.00/1.01    inference(flattening,[],[f29])).
% 3.00/1.01  
% 3.00/1.01  fof(f35,plain,(
% 3.00/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k13_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3))) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k13_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 3.00/1.01    inference(nnf_transformation,[],[f30])).
% 3.00/1.01  
% 3.00/1.01  fof(f36,plain,(
% 3.00/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k13_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k13_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 3.00/1.01    inference(flattening,[],[f35])).
% 3.00/1.01  
% 3.00/1.01  fof(f37,plain,(
% 3.00/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k13_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k13_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 3.00/1.01    inference(rectify,[],[f36])).
% 3.00/1.01  
% 3.00/1.01  fof(f38,plain,(
% 3.00/1.01    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,X3,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))))),
% 3.00/1.01    introduced(choice_axiom,[])).
% 3.00/1.01  
% 3.00/1.01  fof(f39,plain,(
% 3.00/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k13_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,X3,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK0(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k13_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 3.00/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 3.00/1.01  
% 3.00/1.01  fof(f52,plain,(
% 3.00/1.01    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X1,X3) | k13_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 3.00/1.01    inference(cnf_transformation,[],[f39])).
% 3.00/1.01  
% 3.00/1.01  fof(f73,plain,(
% 3.00/1.01    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2)) | ~m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 3.00/1.01    inference(equality_resolution,[],[f52])).
% 3.00/1.01  
% 3.00/1.01  fof(f53,plain,(
% 3.00/1.01    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X2,X3) | k13_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 3.00/1.01    inference(cnf_transformation,[],[f39])).
% 3.00/1.01  
% 3.00/1.01  fof(f72,plain,(
% 3.00/1.01    ( ! [X2,X0,X1] : (r1_orders_2(X0,X2,k13_lattice3(X0,X1,X2)) | ~m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 3.00/1.01    inference(equality_resolution,[],[f53])).
% 3.00/1.01  
% 3.00/1.01  cnf(c_20,plain,
% 3.00/1.01      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.00/1.01      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.01      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.01      | r1_tarski(X1,X2)
% 3.00/1.01      | v1_xboole_0(X0) ),
% 3.00/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_25,negated_conjecture,
% 3.00/1.01      ( ~ v1_xboole_0(sK1) ),
% 3.00/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_271,plain,
% 3.00/1.01      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.00/1.01      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.01      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.01      | r1_tarski(X1,X2)
% 3.00/1.01      | sK1 != X0 ),
% 3.00/1.01      inference(resolution_lifted,[status(thm)],[c_20,c_25]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_272,plain,
% 3.00/1.01      ( ~ r3_orders_2(k2_yellow_1(sK1),X0,X1)
% 3.00/1.01      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK1)))
% 3.00/1.01      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 3.00/1.01      | r1_tarski(X0,X1) ),
% 3.00/1.01      inference(unflattening,[status(thm)],[c_271]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2714,plain,
% 3.00/1.01      ( ~ r3_orders_2(k2_yellow_1(sK1),X0,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
% 3.00/1.01      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 3.00/1.01      | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 3.00/1.01      | r1_tarski(X0,k13_lattice3(k2_yellow_1(sK1),sK2,sK3)) ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_272]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_8498,plain,
% 3.00/1.01      ( ~ r3_orders_2(k2_yellow_1(sK1),sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
% 3.00/1.01      | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 3.00/1.01      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
% 3.00/1.01      | r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3)) ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_2714]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_8495,plain,
% 3.00/1.01      ( ~ r3_orders_2(k2_yellow_1(sK1),sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
% 3.00/1.01      | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 3.00/1.01      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
% 3.00/1.01      | r1_tarski(sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3)) ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_2714]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_23,negated_conjecture,
% 3.00/1.01      ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) ),
% 3.00/1.01      inference(cnf_transformation,[],[f68]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2128,plain,
% 3.00/1.01      ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_18,plain,
% 3.00/1.01      ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
% 3.00/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2138,plain,
% 3.00/1.01      ( m1_subset_1(sK2,sK1) = iProver_top ),
% 3.00/1.01      inference(demodulation,[status(thm)],[c_2128,c_18]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_22,negated_conjecture,
% 3.00/1.01      ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) ),
% 3.00/1.01      inference(cnf_transformation,[],[f69]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2129,plain,
% 3.00/1.01      ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1))) = iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2141,plain,
% 3.00/1.01      ( m1_subset_1(sK3,sK1) = iProver_top ),
% 3.00/1.01      inference(demodulation,[status(thm)],[c_2129,c_18]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_5,plain,
% 3.00/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.00/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.00/1.01      | ~ v5_orders_2(X1)
% 3.00/1.01      | ~ v1_lattice3(X1)
% 3.00/1.01      | ~ l1_orders_2(X1)
% 3.00/1.01      | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0) ),
% 3.00/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_14,plain,
% 3.00/1.01      ( l1_orders_2(k2_yellow_1(X0)) ),
% 3.00/1.01      inference(cnf_transformation,[],[f59]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_776,plain,
% 3.00/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.00/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.00/1.01      | ~ v5_orders_2(X1)
% 3.00/1.01      | ~ v1_lattice3(X1)
% 3.00/1.01      | k10_lattice3(X1,X2,X0) = k13_lattice3(X1,X2,X0)
% 3.00/1.01      | k2_yellow_1(X3) != X1 ),
% 3.00/1.01      inference(resolution_lifted,[status(thm)],[c_5,c_14]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_777,plain,
% 3.00/1.01      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
% 3.00/1.01      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
% 3.00/1.01      | ~ v5_orders_2(k2_yellow_1(X1))
% 3.00/1.01      | ~ v1_lattice3(k2_yellow_1(X1))
% 3.00/1.01      | k10_lattice3(k2_yellow_1(X1),X0,X2) = k13_lattice3(k2_yellow_1(X1),X0,X2) ),
% 3.00/1.01      inference(unflattening,[status(thm)],[c_776]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_15,plain,
% 3.00/1.01      ( v5_orders_2(k2_yellow_1(X0)) ),
% 3.00/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_791,plain,
% 3.00/1.01      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
% 3.00/1.01      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
% 3.00/1.01      | ~ v1_lattice3(k2_yellow_1(X1))
% 3.00/1.01      | k10_lattice3(k2_yellow_1(X1),X2,X0) = k13_lattice3(k2_yellow_1(X1),X2,X0) ),
% 3.00/1.01      inference(forward_subsumption_resolution,
% 3.00/1.01                [status(thm)],
% 3.00/1.01                [c_777,c_15]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2116,plain,
% 3.00/1.01      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k13_lattice3(k2_yellow_1(X0),X1,X2)
% 3.00/1.01      | m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.00/1.01      | m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 3.00/1.01      | v1_lattice3(k2_yellow_1(X0)) != iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_791]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2197,plain,
% 3.00/1.01      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k13_lattice3(k2_yellow_1(X0),X1,X2)
% 3.00/1.01      | m1_subset_1(X2,X0) != iProver_top
% 3.00/1.01      | m1_subset_1(X1,X0) != iProver_top
% 3.00/1.01      | v1_lattice3(k2_yellow_1(X0)) != iProver_top ),
% 3.00/1.01      inference(light_normalisation,[status(thm)],[c_2116,c_18]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_3229,plain,
% 3.00/1.01      ( k10_lattice3(k2_yellow_1(sK1),X0,sK3) = k13_lattice3(k2_yellow_1(sK1),X0,sK3)
% 3.00/1.01      | m1_subset_1(X0,sK1) != iProver_top
% 3.00/1.02      | v1_lattice3(k2_yellow_1(sK1)) != iProver_top ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_2141,c_2197]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_24,negated_conjecture,
% 3.00/1.02      ( v1_lattice3(k2_yellow_1(sK1)) ),
% 3.00/1.02      inference(cnf_transformation,[],[f67]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_27,plain,
% 3.00/1.02      ( v1_lattice3(k2_yellow_1(sK1)) = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_3555,plain,
% 3.00/1.02      ( m1_subset_1(X0,sK1) != iProver_top
% 3.00/1.02      | k10_lattice3(k2_yellow_1(sK1),X0,sK3) = k13_lattice3(k2_yellow_1(sK1),X0,sK3) ),
% 3.00/1.02      inference(global_propositional_subsumption,
% 3.00/1.02                [status(thm)],
% 3.00/1.02                [c_3229,c_27]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_3556,plain,
% 3.00/1.02      ( k10_lattice3(k2_yellow_1(sK1),X0,sK3) = k13_lattice3(k2_yellow_1(sK1),X0,sK3)
% 3.00/1.02      | m1_subset_1(X0,sK1) != iProver_top ),
% 3.00/1.02      inference(renaming,[status(thm)],[c_3555]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_3563,plain,
% 3.00/1.02      ( k10_lattice3(k2_yellow_1(sK1),sK2,sK3) = k13_lattice3(k2_yellow_1(sK1),sK2,sK3) ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_2138,c_3556]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_0,plain,
% 3.00/1.02      ( ~ r1_tarski(X0,X1)
% 3.00/1.02      | ~ r1_tarski(X2,X1)
% 3.00/1.02      | r1_tarski(k2_xboole_0(X2,X0),X1) ),
% 3.00/1.02      inference(cnf_transformation,[],[f45]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2131,plain,
% 3.00/1.02      ( r1_tarski(X0,X1) != iProver_top
% 3.00/1.02      | r1_tarski(X2,X1) != iProver_top
% 3.00/1.02      | r1_tarski(k2_xboole_0(X2,X0),X1) = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_21,negated_conjecture,
% 3.00/1.02      ( ~ r1_tarski(k2_xboole_0(sK2,sK3),k10_lattice3(k2_yellow_1(sK1),sK2,sK3)) ),
% 3.00/1.02      inference(cnf_transformation,[],[f70]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2130,plain,
% 3.00/1.02      ( r1_tarski(k2_xboole_0(sK2,sK3),k10_lattice3(k2_yellow_1(sK1),sK2,sK3)) != iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2803,plain,
% 3.00/1.02      ( r1_tarski(sK3,k10_lattice3(k2_yellow_1(sK1),sK2,sK3)) != iProver_top
% 3.00/1.02      | r1_tarski(sK2,k10_lattice3(k2_yellow_1(sK1),sK2,sK3)) != iProver_top ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_2131,c_2130]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4296,plain,
% 3.00/1.02      ( r1_tarski(sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3)) != iProver_top
% 3.00/1.02      | r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3)) != iProver_top ),
% 3.00/1.02      inference(demodulation,[status(thm)],[c_3563,c_2803]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4304,plain,
% 3.00/1.02      ( ~ r1_tarski(sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
% 3.00/1.02      | ~ r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3)) ),
% 3.00/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_4296]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_3,plain,
% 3.00/1.02      ( ~ v1_lattice3(X0) | ~ v2_struct_0(X0) | ~ l1_orders_2(X0) ),
% 3.00/1.02      inference(cnf_transformation,[],[f48]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1,plain,
% 3.00/1.02      ( ~ r1_orders_2(X0,X1,X2)
% 3.00/1.02      | r3_orders_2(X0,X1,X2)
% 3.00/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.00/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.00/1.02      | v2_struct_0(X0)
% 3.00/1.02      | ~ v3_orders_2(X0)
% 3.00/1.02      | ~ l1_orders_2(X0) ),
% 3.00/1.02      inference(cnf_transformation,[],[f47]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_16,plain,
% 3.00/1.02      ( v3_orders_2(k2_yellow_1(X0)) ),
% 3.00/1.02      inference(cnf_transformation,[],[f60]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_344,plain,
% 3.00/1.02      ( ~ r1_orders_2(X0,X1,X2)
% 3.00/1.02      | r3_orders_2(X0,X1,X2)
% 3.00/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.00/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.00/1.02      | v2_struct_0(X0)
% 3.00/1.02      | ~ l1_orders_2(X0)
% 3.00/1.02      | k2_yellow_1(X3) != X0 ),
% 3.00/1.02      inference(resolution_lifted,[status(thm)],[c_1,c_16]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_345,plain,
% 3.00/1.02      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 3.00/1.02      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.00/1.02      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.02      | v2_struct_0(k2_yellow_1(X0))
% 3.00/1.02      | ~ l1_orders_2(k2_yellow_1(X0)) ),
% 3.00/1.02      inference(unflattening,[status(thm)],[c_344]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_349,plain,
% 3.00/1.02      ( v2_struct_0(k2_yellow_1(X0))
% 3.00/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.02      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.02      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.00/1.02      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2) ),
% 3.00/1.02      inference(global_propositional_subsumption,
% 3.00/1.02                [status(thm)],
% 3.00/1.02                [c_345,c_14]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_350,plain,
% 3.00/1.02      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 3.00/1.02      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.00/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.02      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.02      | v2_struct_0(k2_yellow_1(X0)) ),
% 3.00/1.02      inference(renaming,[status(thm)],[c_349]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_383,plain,
% 3.00/1.02      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 3.00/1.02      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.00/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.02      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.02      | ~ v1_lattice3(X3)
% 3.00/1.02      | ~ l1_orders_2(X3)
% 3.00/1.02      | k2_yellow_1(X0) != X3 ),
% 3.00/1.02      inference(resolution_lifted,[status(thm)],[c_3,c_350]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_384,plain,
% 3.00/1.02      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 3.00/1.02      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.00/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.02      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.02      | ~ v1_lattice3(k2_yellow_1(X0))
% 3.00/1.02      | ~ l1_orders_2(k2_yellow_1(X0)) ),
% 3.00/1.02      inference(unflattening,[status(thm)],[c_383]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_388,plain,
% 3.00/1.02      ( ~ v1_lattice3(k2_yellow_1(X0))
% 3.00/1.02      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.02      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.00/1.02      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2) ),
% 3.00/1.02      inference(global_propositional_subsumption,
% 3.00/1.02                [status(thm)],
% 3.00/1.02                [c_384,c_14]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_389,plain,
% 3.00/1.02      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 3.00/1.02      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 3.00/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.02      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.02      | ~ v1_lattice3(k2_yellow_1(X0)) ),
% 3.00/1.02      inference(renaming,[status(thm)],[c_388]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2463,plain,
% 3.00/1.02      ( ~ r1_orders_2(k2_yellow_1(sK1),sK2,X0)
% 3.00/1.02      | r3_orders_2(k2_yellow_1(sK1),sK2,X0)
% 3.00/1.02      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 3.00/1.02      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
% 3.00/1.02      | ~ v1_lattice3(k2_yellow_1(sK1)) ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_389]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_3217,plain,
% 3.00/1.02      ( ~ r1_orders_2(k2_yellow_1(sK1),sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
% 3.00/1.02      | r3_orders_2(k2_yellow_1(sK1),sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
% 3.00/1.02      | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 3.00/1.02      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
% 3.00/1.02      | ~ v1_lattice3(k2_yellow_1(sK1)) ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_2463]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2458,plain,
% 3.00/1.02      ( ~ r1_orders_2(k2_yellow_1(sK1),sK3,X0)
% 3.00/1.02      | r3_orders_2(k2_yellow_1(sK1),sK3,X0)
% 3.00/1.02      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 3.00/1.02      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
% 3.00/1.02      | ~ v1_lattice3(k2_yellow_1(sK1)) ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_389]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_3185,plain,
% 3.00/1.02      ( ~ r1_orders_2(k2_yellow_1(sK1),sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
% 3.00/1.02      | r3_orders_2(k2_yellow_1(sK1),sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
% 3.00/1.02      | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 3.00/1.02      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
% 3.00/1.02      | ~ v1_lattice3(k2_yellow_1(sK1)) ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_2458]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4,plain,
% 3.00/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.00/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.00/1.02      | m1_subset_1(k13_lattice3(X1,X2,X0),u1_struct_0(X1))
% 3.00/1.02      | ~ v5_orders_2(X1)
% 3.00/1.02      | ~ v1_lattice3(X1)
% 3.00/1.02      | ~ l1_orders_2(X1) ),
% 3.00/1.02      inference(cnf_transformation,[],[f49]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_799,plain,
% 3.00/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.00/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.00/1.02      | m1_subset_1(k13_lattice3(X1,X2,X0),u1_struct_0(X1))
% 3.00/1.02      | ~ v5_orders_2(X1)
% 3.00/1.02      | ~ v1_lattice3(X1)
% 3.00/1.02      | k2_yellow_1(X3) != X1 ),
% 3.00/1.02      inference(resolution_lifted,[status(thm)],[c_4,c_14]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_800,plain,
% 3.00/1.02      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
% 3.00/1.02      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
% 3.00/1.02      | m1_subset_1(k13_lattice3(k2_yellow_1(X1),X0,X2),u1_struct_0(k2_yellow_1(X1)))
% 3.00/1.02      | ~ v5_orders_2(k2_yellow_1(X1))
% 3.00/1.02      | ~ v1_lattice3(k2_yellow_1(X1)) ),
% 3.00/1.02      inference(unflattening,[status(thm)],[c_799]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_814,plain,
% 3.00/1.02      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
% 3.00/1.02      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
% 3.00/1.02      | m1_subset_1(k13_lattice3(k2_yellow_1(X1),X2,X0),u1_struct_0(k2_yellow_1(X1)))
% 3.00/1.02      | ~ v1_lattice3(k2_yellow_1(X1)) ),
% 3.00/1.02      inference(forward_subsumption_resolution,
% 3.00/1.02                [status(thm)],
% 3.00/1.02                [c_800,c_15]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_13,plain,
% 3.00/1.02      ( r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))
% 3.00/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.00/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.00/1.02      | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
% 3.00/1.02      | ~ v5_orders_2(X0)
% 3.00/1.02      | ~ v1_lattice3(X0)
% 3.00/1.02      | ~ l1_orders_2(X0) ),
% 3.00/1.02      inference(cnf_transformation,[],[f73]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_527,plain,
% 3.00/1.02      ( r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))
% 3.00/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.00/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.00/1.02      | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
% 3.00/1.02      | ~ v5_orders_2(X0)
% 3.00/1.02      | ~ v1_lattice3(X0)
% 3.00/1.02      | k2_yellow_1(X3) != X0 ),
% 3.00/1.02      inference(resolution_lifted,[status(thm)],[c_13,c_14]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_528,plain,
% 3.00/1.02      ( r1_orders_2(k2_yellow_1(X0),X1,k13_lattice3(k2_yellow_1(X0),X1,X2))
% 3.00/1.02      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.02      | ~ m1_subset_1(k13_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.02      | ~ v5_orders_2(k2_yellow_1(X0))
% 3.00/1.02      | ~ v1_lattice3(k2_yellow_1(X0)) ),
% 3.00/1.02      inference(unflattening,[status(thm)],[c_527]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_532,plain,
% 3.00/1.02      ( ~ m1_subset_1(k13_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.02      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.02      | r1_orders_2(k2_yellow_1(X0),X1,k13_lattice3(k2_yellow_1(X0),X1,X2))
% 3.00/1.02      | ~ v1_lattice3(k2_yellow_1(X0)) ),
% 3.00/1.02      inference(global_propositional_subsumption,
% 3.00/1.02                [status(thm)],
% 3.00/1.02                [c_528,c_15]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_533,plain,
% 3.00/1.02      ( r1_orders_2(k2_yellow_1(X0),X1,k13_lattice3(k2_yellow_1(X0),X1,X2))
% 3.00/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.02      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.02      | ~ m1_subset_1(k13_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.02      | ~ v1_lattice3(k2_yellow_1(X0)) ),
% 3.00/1.02      inference(renaming,[status(thm)],[c_532]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_819,plain,
% 3.00/1.02      ( r1_orders_2(k2_yellow_1(X0),X1,k13_lattice3(k2_yellow_1(X0),X1,X2))
% 3.00/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.02      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.02      | ~ v1_lattice3(k2_yellow_1(X0)) ),
% 3.00/1.02      inference(backward_subsumption_resolution,
% 3.00/1.02                [status(thm)],
% 3.00/1.02                [c_814,c_533]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2453,plain,
% 3.00/1.02      ( r1_orders_2(k2_yellow_1(sK1),sK2,k13_lattice3(k2_yellow_1(sK1),sK2,X0))
% 3.00/1.02      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 3.00/1.02      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
% 3.00/1.02      | ~ v1_lattice3(k2_yellow_1(sK1)) ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_819]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2789,plain,
% 3.00/1.02      ( r1_orders_2(k2_yellow_1(sK1),sK2,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
% 3.00/1.02      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
% 3.00/1.02      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
% 3.00/1.02      | ~ v1_lattice3(k2_yellow_1(sK1)) ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_2453]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_12,plain,
% 3.00/1.02      ( r1_orders_2(X0,X1,k13_lattice3(X0,X2,X1))
% 3.00/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.00/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.00/1.02      | ~ m1_subset_1(k13_lattice3(X0,X2,X1),u1_struct_0(X0))
% 3.00/1.02      | ~ v5_orders_2(X0)
% 3.00/1.02      | ~ v1_lattice3(X0)
% 3.00/1.02      | ~ l1_orders_2(X0) ),
% 3.00/1.02      inference(cnf_transformation,[],[f72]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_554,plain,
% 3.00/1.02      ( r1_orders_2(X0,X1,k13_lattice3(X0,X2,X1))
% 3.00/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.00/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.00/1.02      | ~ m1_subset_1(k13_lattice3(X0,X2,X1),u1_struct_0(X0))
% 3.00/1.02      | ~ v5_orders_2(X0)
% 3.00/1.02      | ~ v1_lattice3(X0)
% 3.00/1.02      | k2_yellow_1(X3) != X0 ),
% 3.00/1.02      inference(resolution_lifted,[status(thm)],[c_12,c_14]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_555,plain,
% 3.00/1.02      ( r1_orders_2(k2_yellow_1(X0),X1,k13_lattice3(k2_yellow_1(X0),X2,X1))
% 3.00/1.02      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.02      | ~ m1_subset_1(k13_lattice3(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.02      | ~ v5_orders_2(k2_yellow_1(X0))
% 3.00/1.02      | ~ v1_lattice3(k2_yellow_1(X0)) ),
% 3.00/1.02      inference(unflattening,[status(thm)],[c_554]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_557,plain,
% 3.00/1.02      ( ~ m1_subset_1(k13_lattice3(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.02      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.02      | r1_orders_2(k2_yellow_1(X0),X1,k13_lattice3(k2_yellow_1(X0),X2,X1))
% 3.00/1.02      | ~ v1_lattice3(k2_yellow_1(X0)) ),
% 3.00/1.02      inference(global_propositional_subsumption,
% 3.00/1.02                [status(thm)],
% 3.00/1.02                [c_555,c_15]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_558,plain,
% 3.00/1.02      ( r1_orders_2(k2_yellow_1(X0),X1,k13_lattice3(k2_yellow_1(X0),X2,X1))
% 3.00/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.02      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.02      | ~ m1_subset_1(k13_lattice3(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.02      | ~ v1_lattice3(k2_yellow_1(X0)) ),
% 3.00/1.02      inference(renaming,[status(thm)],[c_557]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_818,plain,
% 3.00/1.02      ( r1_orders_2(k2_yellow_1(X0),X1,k13_lattice3(k2_yellow_1(X0),X2,X1))
% 3.00/1.02      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.02      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 3.00/1.02      | ~ v1_lattice3(k2_yellow_1(X0)) ),
% 3.00/1.02      inference(backward_subsumption_resolution,
% 3.00/1.02                [status(thm)],
% 3.00/1.02                [c_814,c_558]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2438,plain,
% 3.00/1.02      ( r1_orders_2(k2_yellow_1(sK1),sK3,k13_lattice3(k2_yellow_1(sK1),X0,sK3))
% 3.00/1.02      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 3.00/1.02      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
% 3.00/1.02      | ~ v1_lattice3(k2_yellow_1(sK1)) ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_818]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2758,plain,
% 3.00/1.02      ( r1_orders_2(k2_yellow_1(sK1),sK3,k13_lattice3(k2_yellow_1(sK1),sK2,sK3))
% 3.00/1.02      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
% 3.00/1.02      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
% 3.00/1.02      | ~ v1_lattice3(k2_yellow_1(sK1)) ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_2438]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2428,plain,
% 3.00/1.02      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
% 3.00/1.02      | m1_subset_1(k13_lattice3(k2_yellow_1(sK1),X0,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 3.00/1.02      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
% 3.00/1.02      | ~ v1_lattice3(k2_yellow_1(sK1)) ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_814]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2578,plain,
% 3.00/1.02      ( m1_subset_1(k13_lattice3(k2_yellow_1(sK1),sK2,sK3),u1_struct_0(k2_yellow_1(sK1)))
% 3.00/1.02      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK1)))
% 3.00/1.02      | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK1)))
% 3.00/1.02      | ~ v1_lattice3(k2_yellow_1(sK1)) ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_2428]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(contradiction,plain,
% 3.00/1.02      ( $false ),
% 3.00/1.02      inference(minisat,
% 3.00/1.02                [status(thm)],
% 3.00/1.02                [c_8498,c_8495,c_4304,c_3217,c_3185,c_2789,c_2758,c_2578,
% 3.00/1.02                 c_22,c_23,c_24]) ).
% 3.00/1.02  
% 3.00/1.02  
% 3.00/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.00/1.02  
% 3.00/1.02  ------                               Statistics
% 3.00/1.02  
% 3.00/1.02  ------ General
% 3.00/1.02  
% 3.00/1.02  abstr_ref_over_cycles:                  0
% 3.00/1.02  abstr_ref_under_cycles:                 0
% 3.00/1.02  gc_basic_clause_elim:                   0
% 3.00/1.02  forced_gc_time:                         0
% 3.00/1.02  parsing_time:                           0.007
% 3.00/1.02  unif_index_cands_time:                  0.
% 3.00/1.02  unif_index_add_time:                    0.
% 3.00/1.02  orderings_time:                         0.
% 3.00/1.02  out_proof_time:                         0.009
% 3.00/1.02  total_time:                             0.311
% 3.00/1.02  num_of_symbols:                         52
% 3.00/1.02  num_of_terms:                           9200
% 3.00/1.02  
% 3.00/1.02  ------ Preprocessing
% 3.00/1.02  
% 3.00/1.02  num_of_splits:                          0
% 3.00/1.02  num_of_split_atoms:                     0
% 3.00/1.02  num_of_reused_defs:                     0
% 3.00/1.02  num_eq_ax_congr_red:                    28
% 3.00/1.02  num_of_sem_filtered_clauses:            1
% 3.00/1.02  num_of_subtypes:                        0
% 3.00/1.02  monotx_restored_types:                  0
% 3.00/1.02  sat_num_of_epr_types:                   0
% 3.00/1.02  sat_num_of_non_cyclic_types:            0
% 3.00/1.02  sat_guarded_non_collapsed_types:        0
% 3.00/1.02  num_pure_diseq_elim:                    0
% 3.00/1.02  simp_replaced_by:                       0
% 3.00/1.02  res_preprocessed:                       118
% 3.00/1.02  prep_upred:                             0
% 3.00/1.02  prep_unflattend:                        24
% 3.00/1.02  smt_new_axioms:                         0
% 3.00/1.02  pred_elim_cands:                        5
% 3.00/1.02  pred_elim:                              5
% 3.00/1.02  pred_elim_cl:                           5
% 3.00/1.02  pred_elim_cycles:                       9
% 3.00/1.02  merged_defs:                            0
% 3.00/1.02  merged_defs_ncl:                        0
% 3.00/1.02  bin_hyper_res:                          0
% 3.00/1.02  prep_cycles:                            4
% 3.00/1.02  pred_elim_time:                         0.037
% 3.00/1.02  splitting_time:                         0.
% 3.00/1.02  sem_filter_time:                        0.
% 3.00/1.02  monotx_time:                            0.001
% 3.00/1.02  subtype_inf_time:                       0.
% 3.00/1.02  
% 3.00/1.02  ------ Problem properties
% 3.00/1.02  
% 3.00/1.02  clauses:                                21
% 3.00/1.02  conjectures:                            4
% 3.00/1.02  epr:                                    0
% 3.00/1.02  horn:                                   18
% 3.00/1.02  ground:                                 4
% 3.00/1.02  unary:                                  6
% 3.00/1.02  binary:                                 0
% 3.00/1.02  lits:                                   87
% 3.00/1.02  lits_eq:                                8
% 3.00/1.02  fd_pure:                                0
% 3.00/1.02  fd_pseudo:                              0
% 3.00/1.02  fd_cond:                                0
% 3.00/1.02  fd_pseudo_cond:                         4
% 3.00/1.02  ac_symbols:                             0
% 3.00/1.02  
% 3.00/1.02  ------ Propositional Solver
% 3.00/1.02  
% 3.00/1.02  prop_solver_calls:                      28
% 3.00/1.02  prop_fast_solver_calls:                 1470
% 3.00/1.02  smt_solver_calls:                       0
% 3.00/1.02  smt_fast_solver_calls:                  0
% 3.00/1.02  prop_num_of_clauses:                    3654
% 3.00/1.02  prop_preprocess_simplified:             8343
% 3.00/1.02  prop_fo_subsumed:                       21
% 3.00/1.02  prop_solver_time:                       0.
% 3.00/1.02  smt_solver_time:                        0.
% 3.00/1.02  smt_fast_solver_time:                   0.
% 3.00/1.02  prop_fast_solver_time:                  0.
% 3.00/1.02  prop_unsat_core_time:                   0.
% 3.00/1.02  
% 3.00/1.02  ------ QBF
% 3.00/1.02  
% 3.00/1.02  qbf_q_res:                              0
% 3.00/1.02  qbf_num_tautologies:                    0
% 3.00/1.02  qbf_prep_cycles:                        0
% 3.00/1.02  
% 3.00/1.02  ------ BMC1
% 3.00/1.02  
% 3.00/1.02  bmc1_current_bound:                     -1
% 3.00/1.02  bmc1_last_solved_bound:                 -1
% 3.00/1.02  bmc1_unsat_core_size:                   -1
% 3.00/1.02  bmc1_unsat_core_parents_size:           -1
% 3.00/1.02  bmc1_merge_next_fun:                    0
% 3.00/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.00/1.02  
% 3.00/1.02  ------ Instantiation
% 3.00/1.02  
% 3.00/1.02  inst_num_of_clauses:                    948
% 3.00/1.02  inst_num_in_passive:                    359
% 3.00/1.02  inst_num_in_active:                     287
% 3.00/1.02  inst_num_in_unprocessed:                301
% 3.00/1.02  inst_num_of_loops:                      313
% 3.00/1.02  inst_num_of_learning_restarts:          0
% 3.00/1.02  inst_num_moves_active_passive:          24
% 3.00/1.02  inst_lit_activity:                      0
% 3.00/1.02  inst_lit_activity_moves:                1
% 3.00/1.02  inst_num_tautologies:                   0
% 3.00/1.02  inst_num_prop_implied:                  0
% 3.00/1.02  inst_num_existing_simplified:           0
% 3.00/1.02  inst_num_eq_res_simplified:             0
% 3.00/1.02  inst_num_child_elim:                    0
% 3.00/1.02  inst_num_of_dismatching_blockings:      218
% 3.00/1.02  inst_num_of_non_proper_insts:           520
% 3.00/1.02  inst_num_of_duplicates:                 0
% 3.00/1.02  inst_inst_num_from_inst_to_res:         0
% 3.00/1.02  inst_dismatching_checking_time:         0.
% 3.00/1.02  
% 3.00/1.02  ------ Resolution
% 3.00/1.02  
% 3.00/1.02  res_num_of_clauses:                     0
% 3.00/1.02  res_num_in_passive:                     0
% 3.00/1.02  res_num_in_active:                      0
% 3.00/1.02  res_num_of_loops:                       122
% 3.00/1.02  res_forward_subset_subsumed:            3
% 3.00/1.02  res_backward_subset_subsumed:           0
% 3.00/1.02  res_forward_subsumed:                   0
% 3.00/1.02  res_backward_subsumed:                  0
% 3.00/1.02  res_forward_subsumption_resolution:     3
% 3.00/1.02  res_backward_subsumption_resolution:    2
% 3.00/1.02  res_clause_to_clause_subsumption:       821
% 3.00/1.02  res_orphan_elimination:                 0
% 3.00/1.02  res_tautology_del:                      11
% 3.00/1.02  res_num_eq_res_simplified:              0
% 3.00/1.02  res_num_sel_changes:                    0
% 3.00/1.02  res_moves_from_active_to_pass:          0
% 3.00/1.02  
% 3.00/1.02  ------ Superposition
% 3.00/1.02  
% 3.00/1.02  sup_time_total:                         0.
% 3.00/1.02  sup_time_generating:                    0.
% 3.00/1.02  sup_time_sim_full:                      0.
% 3.00/1.02  sup_time_sim_immed:                     0.
% 3.00/1.02  
% 3.00/1.02  sup_num_of_clauses:                     110
% 3.00/1.02  sup_num_in_active:                      59
% 3.00/1.02  sup_num_in_passive:                     51
% 3.00/1.02  sup_num_of_loops:                       62
% 3.00/1.02  sup_fw_superposition:                   89
% 3.00/1.02  sup_bw_superposition:                   13
% 3.00/1.02  sup_immediate_simplified:               16
% 3.00/1.02  sup_given_eliminated:                   0
% 3.00/1.02  comparisons_done:                       0
% 3.00/1.02  comparisons_avoided:                    0
% 3.00/1.02  
% 3.00/1.02  ------ Simplifications
% 3.00/1.02  
% 3.00/1.02  
% 3.00/1.02  sim_fw_subset_subsumed:                 0
% 3.00/1.02  sim_bw_subset_subsumed:                 0
% 3.00/1.02  sim_fw_subsumed:                        5
% 3.00/1.02  sim_bw_subsumed:                        0
% 3.00/1.02  sim_fw_subsumption_res:                 1
% 3.00/1.02  sim_bw_subsumption_res:                 0
% 3.00/1.02  sim_tautology_del:                      1
% 3.00/1.02  sim_eq_tautology_del:                   2
% 3.00/1.02  sim_eq_res_simp:                        0
% 3.00/1.02  sim_fw_demodulated:                     5
% 3.00/1.02  sim_bw_demodulated:                     3
% 3.00/1.02  sim_light_normalised:                   22
% 3.00/1.02  sim_joinable_taut:                      0
% 3.00/1.02  sim_joinable_simp:                      0
% 3.00/1.02  sim_ac_normalised:                      0
% 3.00/1.02  sim_smt_subsumption:                    0
% 3.00/1.02  
%------------------------------------------------------------------------------
