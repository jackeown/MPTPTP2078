%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:04 EST 2020

% Result     : Theorem 1.26s
% Output     : CNFRefutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 497 expanded)
%              Number of clauses        :   74 ( 121 expanded)
%              Number of leaves         :   18 ( 136 expanded)
%              Depth                    :   21
%              Number of atoms          :  611 (2829 expanded)
%              Number of equality atoms :  101 ( 469 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m2_orders_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
     => m2_orders_2(sK3(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m2_orders_2(sK3(X0,X1),X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f38])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m2_orders_2(sK3(X0,X1),X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
     => ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,sK5))
        & m1_orders_1(sK5,k1_orders_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
            & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(sK4,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK4))) )
      & l1_orders_2(sK4)
      & v5_orders_2(sK4)
      & v4_orders_2(sK4)
      & v3_orders_2(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK4,sK5))
    & m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4)))
    & l1_orders_2(sK4)
    & v5_orders_2(sK4)
    & v4_orders_2(sK4)
    & v3_orders_2(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f29,f41,f40])).

fof(f63,plain,(
    m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f42])).

fof(f62,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f58,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f59,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f60,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f61,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ? [X3] :
                    ( ( ~ m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) )
                    & ( m2_orders_2(X3,X0,X1)
                      | r2_hidden(X3,X2) ) ) )
              & ( ! [X3] :
                    ( ( r2_hidden(X3,X2)
                      | ~ m2_orders_2(X3,X0,X1) )
                    & ( m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ? [X3] :
                    ( ( ~ m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) )
                    & ( m2_orders_2(X3,X0,X1)
                      | r2_hidden(X3,X2) ) ) )
              & ( ! [X4] :
                    ( ( r2_hidden(X4,X2)
                      | ~ m2_orders_2(X4,X0,X1) )
                    & ( m2_orders_2(X4,X0,X1)
                      | ~ r2_hidden(X4,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ m2_orders_2(X3,X0,X1)
            | ~ r2_hidden(X3,X2) )
          & ( m2_orders_2(X3,X0,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ m2_orders_2(sK2(X0,X1,X2),X0,X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( m2_orders_2(sK2(X0,X1,X2),X0,X1)
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ( ( ~ m2_orders_2(sK2(X0,X1,X2),X0,X1)
                    | ~ r2_hidden(sK2(X0,X1,X2),X2) )
                  & ( m2_orders_2(sK2(X0,X1,X2),X0,X1)
                    | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
              & ( ! [X4] :
                    ( ( r2_hidden(X4,X2)
                      | ~ m2_orders_2(X4,X0,X1) )
                    & ( m2_orders_2(X4,X0,X1)
                      | ~ r2_hidden(X4,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ m2_orders_2(X4,X0,X1)
      | k4_orders_2(X0,X1) != X2
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f65,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_orders_2(X0,X1))
      | ~ m2_orders_2(X4,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f64,plain,(
    k1_xboole_0 = k3_tarski(k4_orders_2(sK4,sK5)) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_xboole_0(X2,X1) )
     => r1_xboole_0(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_xboole_0(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_xboole_0(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_xboole_0(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ( ~ r1_xboole_0(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f32])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f15,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f30])).

fof(f43,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k4_orders_2(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( m2_orders_2(X4,X0,X1)
      | ~ r2_hidden(X4,X2)
      | k4_orders_2(X0,X1) != X2
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( m2_orders_2(X4,X0,X1)
      | ~ r2_hidden(X4,k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ~ r1_xboole_0(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ~ r1_xboole_0(X2,X3)
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ~ r1_xboole_0(X2,X3)
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X2,X3)
      | ~ m2_orders_2(X3,X0,X1)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_12,plain,
    ( m2_orders_2(sK3(X0,X1),X0,X1)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_16,negated_conjecture,
    ( m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_315,plain,
    ( m2_orders_2(sK3(X0,X1),X0,X1)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK4))
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_16])).

cnf(c_316,plain,
    ( m2_orders_2(sK3(X0,sK5),X0,sK5)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_315])).

cnf(c_17,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_688,plain,
    ( m2_orders_2(sK3(X0,sK5),X0,sK5)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK4))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_316,c_17])).

cnf(c_689,plain,
    ( m2_orders_2(sK3(sK4,sK5),sK4,sK5)
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_688])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_20,negated_conjecture,
    ( v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_19,negated_conjecture,
    ( v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_18,negated_conjecture,
    ( v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_691,plain,
    ( m2_orders_2(sK3(sK4,sK5),sK4,sK5)
    | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_689,c_21,c_20,c_19,c_18])).

cnf(c_831,plain,
    ( m2_orders_2(sK3(sK4,sK5),sK4,sK5) ),
    inference(equality_resolution_simp,[status(thm)],[c_691])).

cnf(c_1276,plain,
    ( m2_orders_2(sK3(sK4,sK5),sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_831])).

cnf(c_10,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | r2_hidden(X0,k4_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_471,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | r2_hidden(X0,k4_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK4))
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_16])).

cnf(c_472,plain,
    ( ~ m2_orders_2(X0,X1,sK5)
    | r2_hidden(X0,k4_orders_2(X1,sK5))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_471])).

cnf(c_702,plain,
    ( ~ m2_orders_2(X0,X1,sK5)
    | r2_hidden(X0,k4_orders_2(X1,sK5))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK4))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_472,c_17])).

cnf(c_703,plain,
    ( ~ m2_orders_2(X0,sK4,sK5)
    | r2_hidden(X0,k4_orders_2(sK4,sK5))
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_702])).

cnf(c_707,plain,
    ( ~ m2_orders_2(X0,sK4,sK5)
    | r2_hidden(X0,k4_orders_2(sK4,sK5))
    | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_703,c_21,c_20,c_19,c_18])).

cnf(c_827,plain,
    ( ~ m2_orders_2(X0,sK4,sK5)
    | r2_hidden(X0,k4_orders_2(sK4,sK5)) ),
    inference(equality_resolution_simp,[status(thm)],[c_707])).

cnf(c_865,plain,
    ( ~ m2_orders_2(X0,sK4,sK5)
    | r2_hidden(X0,k4_orders_2(sK4,sK5)) ),
    inference(prop_impl,[status(thm)],[c_827])).

cnf(c_1277,plain,
    ( m2_orders_2(X0,sK4,sK5) != iProver_top
    | r2_hidden(X0,k4_orders_2(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_865])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK4,sK5)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3,plain,
    ( r1_tarski(X0,k3_tarski(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_245,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k3_tarski(X1) != k1_xboole_0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_3])).

cnf(c_246,plain,
    ( ~ r2_hidden(X0,X1)
    | k3_tarski(X1) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_245])).

cnf(c_1282,plain,
    ( k3_tarski(X0) != k1_xboole_0
    | k1_xboole_0 = X1
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_246])).

cnf(c_2509,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(X0,k4_orders_2(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_1282])).

cnf(c_2587,plain,
    ( k1_xboole_0 = X0
    | m2_orders_2(X0,sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1277,c_2509])).

cnf(c_6,plain,
    ( r1_xboole_0(k3_tarski(X0),X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1284,plain,
    ( r1_xboole_0(k3_tarski(X0),X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_236,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_7])).

cnf(c_237,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_236])).

cnf(c_1283,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_237])).

cnf(c_1882,plain,
    ( r1_xboole_0(k3_tarski(k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1284,c_1283])).

cnf(c_4,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1889,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1882,c_4])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_13,plain,
    ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v1_xboole_0(k4_orders_2(X1,X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_501,plain,
    ( v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_xboole_0(k4_orders_2(X0,X1))
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK4))
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_16])).

cnf(c_502,plain,
    ( v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_xboole_0(k4_orders_2(X0,sK5))
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_501])).

cnf(c_626,plain,
    ( v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_xboole_0(k4_orders_2(X0,sK5))
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK4))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_502,c_17])).

cnf(c_627,plain,
    ( v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v1_xboole_0(k4_orders_2(sK4,sK5))
    | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_626])).

cnf(c_629,plain,
    ( ~ v1_xboole_0(k4_orders_2(sK4,sK5))
    | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_627,c_21,c_20,c_19,c_18])).

cnf(c_797,plain,
    ( r2_hidden(sK0(X0),X0)
    | k4_orders_2(sK4,sK5) != X0
    | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4)) ),
    inference(resolution_lifted,[status(thm)],[c_0,c_629])).

cnf(c_798,plain,
    ( r2_hidden(sK0(k4_orders_2(sK4,sK5)),k4_orders_2(sK4,sK5)) ),
    inference(unflattening,[status(thm)],[c_797])).

cnf(c_1280,plain,
    ( r2_hidden(sK0(k4_orders_2(sK4,sK5)),k4_orders_2(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_798])).

cnf(c_2585,plain,
    ( sK0(k4_orders_2(sK4,sK5)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1280,c_2509])).

cnf(c_11,plain,
    ( m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,k4_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_441,plain,
    ( m2_orders_2(X0,X1,X2)
    | ~ r2_hidden(X0,k4_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK4))
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_16])).

cnf(c_442,plain,
    ( m2_orders_2(X0,X1,sK5)
    | ~ r2_hidden(X0,k4_orders_2(X1,sK5))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_441])).

cnf(c_723,plain,
    ( m2_orders_2(X0,X1,sK5)
    | ~ r2_hidden(X0,k4_orders_2(X1,sK5))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK4))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_442,c_17])).

cnf(c_724,plain,
    ( m2_orders_2(X0,sK4,sK5)
    | ~ r2_hidden(X0,k4_orders_2(sK4,sK5))
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_723])).

cnf(c_728,plain,
    ( m2_orders_2(X0,sK4,sK5)
    | ~ r2_hidden(X0,k4_orders_2(sK4,sK5))
    | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_724,c_21,c_20,c_19,c_18])).

cnf(c_823,plain,
    ( m2_orders_2(X0,sK4,sK5)
    | ~ r2_hidden(X0,k4_orders_2(sK4,sK5)) ),
    inference(equality_resolution_simp,[status(thm)],[c_728])).

cnf(c_863,plain,
    ( m2_orders_2(X0,sK4,sK5)
    | ~ r2_hidden(X0,k4_orders_2(sK4,sK5)) ),
    inference(prop_impl,[status(thm)],[c_823])).

cnf(c_1278,plain,
    ( m2_orders_2(X0,sK4,sK5) = iProver_top
    | r2_hidden(X0,k4_orders_2(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_863])).

cnf(c_1697,plain,
    ( m2_orders_2(sK0(k4_orders_2(sK4,sK5)),sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1280,c_1278])).

cnf(c_14,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(X3,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X3,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_408,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(X3,X1,X2)
    | ~ r1_xboole_0(X3,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK4))
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_16])).

cnf(c_409,plain,
    ( ~ m2_orders_2(X0,X1,sK5)
    | ~ m2_orders_2(X2,X1,sK5)
    | ~ r1_xboole_0(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_408])).

cnf(c_744,plain,
    ( ~ m2_orders_2(X0,X1,sK5)
    | ~ m2_orders_2(X2,X1,sK5)
    | ~ r1_xboole_0(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK4))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_409,c_17])).

cnf(c_745,plain,
    ( ~ m2_orders_2(X0,sK4,sK5)
    | ~ m2_orders_2(X1,sK4,sK5)
    | ~ r1_xboole_0(X0,X1)
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_744])).

cnf(c_749,plain,
    ( ~ m2_orders_2(X0,sK4,sK5)
    | ~ m2_orders_2(X1,sK4,sK5)
    | ~ r1_xboole_0(X0,X1)
    | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_745,c_21,c_20,c_19,c_18])).

cnf(c_819,plain,
    ( ~ m2_orders_2(X0,sK4,sK5)
    | ~ m2_orders_2(X1,sK4,sK5)
    | ~ r1_xboole_0(X0,X1) ),
    inference(equality_resolution_simp,[status(thm)],[c_749])).

cnf(c_1279,plain,
    ( m2_orders_2(X0,sK4,sK5) != iProver_top
    | m2_orders_2(X1,sK4,sK5) != iProver_top
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_819])).

cnf(c_1820,plain,
    ( m2_orders_2(X0,sK4,sK5) != iProver_top
    | r1_xboole_0(sK0(k4_orders_2(sK4,sK5)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1697,c_1279])).

cnf(c_2602,plain,
    ( m2_orders_2(X0,sK4,sK5) != iProver_top
    | r1_xboole_0(k1_xboole_0,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2585,c_1820])).

cnf(c_2639,plain,
    ( m2_orders_2(X0,sK4,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2587,c_1889,c_2602])).

cnf(c_2646,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1276,c_2639])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:20:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 1.26/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.26/0.98  
% 1.26/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.26/0.98  
% 1.26/0.98  ------  iProver source info
% 1.26/0.98  
% 1.26/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.26/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.26/0.98  git: non_committed_changes: false
% 1.26/0.98  git: last_make_outside_of_git: false
% 1.26/0.98  
% 1.26/0.98  ------ 
% 1.26/0.98  
% 1.26/0.98  ------ Input Options
% 1.26/0.98  
% 1.26/0.98  --out_options                           all
% 1.26/0.98  --tptp_safe_out                         true
% 1.26/0.98  --problem_path                          ""
% 1.26/0.98  --include_path                          ""
% 1.26/0.98  --clausifier                            res/vclausify_rel
% 1.26/0.98  --clausifier_options                    --mode clausify
% 1.26/0.98  --stdin                                 false
% 1.26/0.98  --stats_out                             all
% 1.26/0.98  
% 1.26/0.98  ------ General Options
% 1.26/0.98  
% 1.26/0.98  --fof                                   false
% 1.26/0.98  --time_out_real                         305.
% 1.26/0.98  --time_out_virtual                      -1.
% 1.26/0.98  --symbol_type_check                     false
% 1.26/0.98  --clausify_out                          false
% 1.26/0.98  --sig_cnt_out                           false
% 1.26/0.98  --trig_cnt_out                          false
% 1.26/0.98  --trig_cnt_out_tolerance                1.
% 1.26/0.98  --trig_cnt_out_sk_spl                   false
% 1.26/0.98  --abstr_cl_out                          false
% 1.26/0.98  
% 1.26/0.98  ------ Global Options
% 1.26/0.98  
% 1.26/0.98  --schedule                              default
% 1.26/0.98  --add_important_lit                     false
% 1.26/0.98  --prop_solver_per_cl                    1000
% 1.26/0.98  --min_unsat_core                        false
% 1.26/0.98  --soft_assumptions                      false
% 1.26/0.98  --soft_lemma_size                       3
% 1.26/0.98  --prop_impl_unit_size                   0
% 1.26/0.98  --prop_impl_unit                        []
% 1.26/0.98  --share_sel_clauses                     true
% 1.26/0.98  --reset_solvers                         false
% 1.26/0.98  --bc_imp_inh                            [conj_cone]
% 1.26/0.98  --conj_cone_tolerance                   3.
% 1.26/0.98  --extra_neg_conj                        none
% 1.26/0.98  --large_theory_mode                     true
% 1.26/0.98  --prolific_symb_bound                   200
% 1.26/0.98  --lt_threshold                          2000
% 1.26/0.98  --clause_weak_htbl                      true
% 1.26/0.98  --gc_record_bc_elim                     false
% 1.26/0.98  
% 1.26/0.98  ------ Preprocessing Options
% 1.26/0.98  
% 1.26/0.98  --preprocessing_flag                    true
% 1.26/0.98  --time_out_prep_mult                    0.1
% 1.26/0.98  --splitting_mode                        input
% 1.26/0.98  --splitting_grd                         true
% 1.26/0.98  --splitting_cvd                         false
% 1.26/0.98  --splitting_cvd_svl                     false
% 1.26/0.98  --splitting_nvd                         32
% 1.26/0.98  --sub_typing                            true
% 1.26/0.98  --prep_gs_sim                           true
% 1.26/0.98  --prep_unflatten                        true
% 1.26/0.98  --prep_res_sim                          true
% 1.26/0.98  --prep_upred                            true
% 1.26/0.98  --prep_sem_filter                       exhaustive
% 1.26/0.98  --prep_sem_filter_out                   false
% 1.26/0.98  --pred_elim                             true
% 1.26/0.98  --res_sim_input                         true
% 1.26/0.98  --eq_ax_congr_red                       true
% 1.26/0.98  --pure_diseq_elim                       true
% 1.26/0.98  --brand_transform                       false
% 1.26/0.98  --non_eq_to_eq                          false
% 1.26/0.98  --prep_def_merge                        true
% 1.26/0.98  --prep_def_merge_prop_impl              false
% 1.26/0.98  --prep_def_merge_mbd                    true
% 1.26/0.98  --prep_def_merge_tr_red                 false
% 1.26/0.98  --prep_def_merge_tr_cl                  false
% 1.26/0.98  --smt_preprocessing                     true
% 1.26/0.98  --smt_ac_axioms                         fast
% 1.26/0.98  --preprocessed_out                      false
% 1.26/0.98  --preprocessed_stats                    false
% 1.26/0.98  
% 1.26/0.98  ------ Abstraction refinement Options
% 1.26/0.98  
% 1.26/0.98  --abstr_ref                             []
% 1.26/0.98  --abstr_ref_prep                        false
% 1.26/0.98  --abstr_ref_until_sat                   false
% 1.26/0.98  --abstr_ref_sig_restrict                funpre
% 1.26/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.26/0.98  --abstr_ref_under                       []
% 1.26/0.98  
% 1.26/0.98  ------ SAT Options
% 1.26/0.98  
% 1.26/0.98  --sat_mode                              false
% 1.26/0.98  --sat_fm_restart_options                ""
% 1.26/0.98  --sat_gr_def                            false
% 1.26/0.98  --sat_epr_types                         true
% 1.26/0.98  --sat_non_cyclic_types                  false
% 1.26/0.98  --sat_finite_models                     false
% 1.26/0.98  --sat_fm_lemmas                         false
% 1.26/0.98  --sat_fm_prep                           false
% 1.26/0.98  --sat_fm_uc_incr                        true
% 1.26/0.98  --sat_out_model                         small
% 1.26/0.98  --sat_out_clauses                       false
% 1.26/0.98  
% 1.26/0.98  ------ QBF Options
% 1.26/0.98  
% 1.26/0.98  --qbf_mode                              false
% 1.26/0.98  --qbf_elim_univ                         false
% 1.26/0.98  --qbf_dom_inst                          none
% 1.26/0.98  --qbf_dom_pre_inst                      false
% 1.26/0.98  --qbf_sk_in                             false
% 1.26/0.98  --qbf_pred_elim                         true
% 1.26/0.98  --qbf_split                             512
% 1.26/0.98  
% 1.26/0.98  ------ BMC1 Options
% 1.26/0.98  
% 1.26/0.98  --bmc1_incremental                      false
% 1.26/0.98  --bmc1_axioms                           reachable_all
% 1.26/0.98  --bmc1_min_bound                        0
% 1.26/0.98  --bmc1_max_bound                        -1
% 1.26/0.98  --bmc1_max_bound_default                -1
% 1.26/0.98  --bmc1_symbol_reachability              true
% 1.26/0.98  --bmc1_property_lemmas                  false
% 1.26/0.98  --bmc1_k_induction                      false
% 1.26/0.98  --bmc1_non_equiv_states                 false
% 1.26/0.98  --bmc1_deadlock                         false
% 1.26/0.98  --bmc1_ucm                              false
% 1.26/0.98  --bmc1_add_unsat_core                   none
% 1.26/0.98  --bmc1_unsat_core_children              false
% 1.26/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.26/0.98  --bmc1_out_stat                         full
% 1.26/0.98  --bmc1_ground_init                      false
% 1.26/0.98  --bmc1_pre_inst_next_state              false
% 1.26/0.98  --bmc1_pre_inst_state                   false
% 1.26/0.98  --bmc1_pre_inst_reach_state             false
% 1.26/0.98  --bmc1_out_unsat_core                   false
% 1.26/0.98  --bmc1_aig_witness_out                  false
% 1.26/0.98  --bmc1_verbose                          false
% 1.26/0.98  --bmc1_dump_clauses_tptp                false
% 1.26/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.26/0.98  --bmc1_dump_file                        -
% 1.26/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.26/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.26/0.98  --bmc1_ucm_extend_mode                  1
% 1.26/0.98  --bmc1_ucm_init_mode                    2
% 1.26/0.98  --bmc1_ucm_cone_mode                    none
% 1.26/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.26/0.98  --bmc1_ucm_relax_model                  4
% 1.26/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.26/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.26/0.98  --bmc1_ucm_layered_model                none
% 1.26/0.98  --bmc1_ucm_max_lemma_size               10
% 1.26/0.98  
% 1.26/0.98  ------ AIG Options
% 1.26/0.98  
% 1.26/0.98  --aig_mode                              false
% 1.26/0.98  
% 1.26/0.98  ------ Instantiation Options
% 1.26/0.98  
% 1.26/0.98  --instantiation_flag                    true
% 1.26/0.98  --inst_sos_flag                         false
% 1.26/0.98  --inst_sos_phase                        true
% 1.26/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.26/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.26/0.98  --inst_lit_sel_side                     num_symb
% 1.26/0.98  --inst_solver_per_active                1400
% 1.26/0.98  --inst_solver_calls_frac                1.
% 1.26/0.98  --inst_passive_queue_type               priority_queues
% 1.26/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.26/0.98  --inst_passive_queues_freq              [25;2]
% 1.26/0.98  --inst_dismatching                      true
% 1.26/0.98  --inst_eager_unprocessed_to_passive     true
% 1.26/0.98  --inst_prop_sim_given                   true
% 1.26/0.98  --inst_prop_sim_new                     false
% 1.26/0.98  --inst_subs_new                         false
% 1.26/0.98  --inst_eq_res_simp                      false
% 1.26/0.98  --inst_subs_given                       false
% 1.26/0.98  --inst_orphan_elimination               true
% 1.26/0.98  --inst_learning_loop_flag               true
% 1.26/0.98  --inst_learning_start                   3000
% 1.26/0.98  --inst_learning_factor                  2
% 1.26/0.98  --inst_start_prop_sim_after_learn       3
% 1.26/0.98  --inst_sel_renew                        solver
% 1.26/0.98  --inst_lit_activity_flag                true
% 1.26/0.98  --inst_restr_to_given                   false
% 1.26/0.98  --inst_activity_threshold               500
% 1.26/0.98  --inst_out_proof                        true
% 1.26/0.98  
% 1.26/0.98  ------ Resolution Options
% 1.26/0.98  
% 1.26/0.98  --resolution_flag                       true
% 1.26/0.98  --res_lit_sel                           adaptive
% 1.26/0.98  --res_lit_sel_side                      none
% 1.26/0.98  --res_ordering                          kbo
% 1.26/0.98  --res_to_prop_solver                    active
% 1.26/0.98  --res_prop_simpl_new                    false
% 1.26/0.98  --res_prop_simpl_given                  true
% 1.26/0.98  --res_passive_queue_type                priority_queues
% 1.26/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.26/0.98  --res_passive_queues_freq               [15;5]
% 1.26/0.98  --res_forward_subs                      full
% 1.26/0.98  --res_backward_subs                     full
% 1.26/0.98  --res_forward_subs_resolution           true
% 1.26/0.98  --res_backward_subs_resolution          true
% 1.26/0.98  --res_orphan_elimination                true
% 1.26/0.98  --res_time_limit                        2.
% 1.26/0.98  --res_out_proof                         true
% 1.26/0.98  
% 1.26/0.98  ------ Superposition Options
% 1.26/0.98  
% 1.26/0.98  --superposition_flag                    true
% 1.26/0.98  --sup_passive_queue_type                priority_queues
% 1.26/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.26/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.26/0.98  --demod_completeness_check              fast
% 1.26/0.98  --demod_use_ground                      true
% 1.26/0.98  --sup_to_prop_solver                    passive
% 1.26/0.98  --sup_prop_simpl_new                    true
% 1.26/0.98  --sup_prop_simpl_given                  true
% 1.26/0.98  --sup_fun_splitting                     false
% 1.26/0.98  --sup_smt_interval                      50000
% 1.26/0.98  
% 1.26/0.98  ------ Superposition Simplification Setup
% 1.26/0.98  
% 1.26/0.98  --sup_indices_passive                   []
% 1.26/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.26/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.26/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.26/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.26/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.26/0.98  --sup_full_bw                           [BwDemod]
% 1.26/0.98  --sup_immed_triv                        [TrivRules]
% 1.26/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.26/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.26/0.98  --sup_immed_bw_main                     []
% 1.26/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.26/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.26/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.26/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.26/0.98  
% 1.26/0.98  ------ Combination Options
% 1.26/0.98  
% 1.26/0.98  --comb_res_mult                         3
% 1.26/0.98  --comb_sup_mult                         2
% 1.26/0.98  --comb_inst_mult                        10
% 1.26/0.98  
% 1.26/0.98  ------ Debug Options
% 1.26/0.98  
% 1.26/0.98  --dbg_backtrace                         false
% 1.26/0.98  --dbg_dump_prop_clauses                 false
% 1.26/0.98  --dbg_dump_prop_clauses_file            -
% 1.26/0.98  --dbg_out_stat                          false
% 1.26/0.98  ------ Parsing...
% 1.26/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.26/0.98  
% 1.26/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 1.26/0.98  
% 1.26/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.26/0.98  
% 1.26/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.26/0.98  ------ Proving...
% 1.26/0.98  ------ Problem Properties 
% 1.26/0.98  
% 1.26/0.98  
% 1.26/0.98  clauses                                 14
% 1.26/0.98  conjectures                             1
% 1.26/0.98  EPR                                     2
% 1.26/0.98  Horn                                    12
% 1.26/0.98  unary                                   5
% 1.26/0.98  binary                                  5
% 1.26/0.98  lits                                    27
% 1.26/0.98  lits eq                                 6
% 1.26/0.98  fd_pure                                 0
% 1.26/0.98  fd_pseudo                               0
% 1.26/0.98  fd_cond                                 3
% 1.26/0.98  fd_pseudo_cond                          0
% 1.26/0.98  AC symbols                              0
% 1.26/0.98  
% 1.26/0.98  ------ Schedule dynamic 5 is on 
% 1.26/0.98  
% 1.26/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.26/0.98  
% 1.26/0.98  
% 1.26/0.98  ------ 
% 1.26/0.98  Current options:
% 1.26/0.98  ------ 
% 1.26/0.98  
% 1.26/0.98  ------ Input Options
% 1.26/0.98  
% 1.26/0.98  --out_options                           all
% 1.26/0.98  --tptp_safe_out                         true
% 1.26/0.98  --problem_path                          ""
% 1.26/0.98  --include_path                          ""
% 1.26/0.98  --clausifier                            res/vclausify_rel
% 1.26/0.98  --clausifier_options                    --mode clausify
% 1.26/0.98  --stdin                                 false
% 1.26/0.98  --stats_out                             all
% 1.26/0.98  
% 1.26/0.98  ------ General Options
% 1.26/0.98  
% 1.26/0.98  --fof                                   false
% 1.26/0.98  --time_out_real                         305.
% 1.26/0.98  --time_out_virtual                      -1.
% 1.26/0.98  --symbol_type_check                     false
% 1.26/0.98  --clausify_out                          false
% 1.26/0.98  --sig_cnt_out                           false
% 1.26/0.98  --trig_cnt_out                          false
% 1.26/0.98  --trig_cnt_out_tolerance                1.
% 1.26/0.98  --trig_cnt_out_sk_spl                   false
% 1.26/0.98  --abstr_cl_out                          false
% 1.26/0.98  
% 1.26/0.98  ------ Global Options
% 1.26/0.98  
% 1.26/0.98  --schedule                              default
% 1.26/0.98  --add_important_lit                     false
% 1.26/0.98  --prop_solver_per_cl                    1000
% 1.26/0.98  --min_unsat_core                        false
% 1.26/0.98  --soft_assumptions                      false
% 1.26/0.98  --soft_lemma_size                       3
% 1.26/0.98  --prop_impl_unit_size                   0
% 1.26/0.98  --prop_impl_unit                        []
% 1.26/0.98  --share_sel_clauses                     true
% 1.26/0.98  --reset_solvers                         false
% 1.26/0.98  --bc_imp_inh                            [conj_cone]
% 1.26/0.98  --conj_cone_tolerance                   3.
% 1.26/0.98  --extra_neg_conj                        none
% 1.26/0.98  --large_theory_mode                     true
% 1.26/0.98  --prolific_symb_bound                   200
% 1.26/0.98  --lt_threshold                          2000
% 1.26/0.98  --clause_weak_htbl                      true
% 1.26/0.98  --gc_record_bc_elim                     false
% 1.26/0.98  
% 1.26/0.98  ------ Preprocessing Options
% 1.26/0.98  
% 1.26/0.98  --preprocessing_flag                    true
% 1.26/0.98  --time_out_prep_mult                    0.1
% 1.26/0.98  --splitting_mode                        input
% 1.26/0.98  --splitting_grd                         true
% 1.26/0.98  --splitting_cvd                         false
% 1.26/0.98  --splitting_cvd_svl                     false
% 1.26/0.98  --splitting_nvd                         32
% 1.26/0.98  --sub_typing                            true
% 1.26/0.98  --prep_gs_sim                           true
% 1.26/0.98  --prep_unflatten                        true
% 1.26/0.98  --prep_res_sim                          true
% 1.26/0.98  --prep_upred                            true
% 1.26/0.98  --prep_sem_filter                       exhaustive
% 1.26/0.98  --prep_sem_filter_out                   false
% 1.26/0.98  --pred_elim                             true
% 1.26/0.98  --res_sim_input                         true
% 1.26/0.98  --eq_ax_congr_red                       true
% 1.26/0.98  --pure_diseq_elim                       true
% 1.26/0.98  --brand_transform                       false
% 1.26/0.98  --non_eq_to_eq                          false
% 1.26/0.98  --prep_def_merge                        true
% 1.26/0.98  --prep_def_merge_prop_impl              false
% 1.26/0.98  --prep_def_merge_mbd                    true
% 1.26/0.98  --prep_def_merge_tr_red                 false
% 1.26/0.98  --prep_def_merge_tr_cl                  false
% 1.26/0.98  --smt_preprocessing                     true
% 1.26/0.98  --smt_ac_axioms                         fast
% 1.26/0.98  --preprocessed_out                      false
% 1.26/0.98  --preprocessed_stats                    false
% 1.26/0.98  
% 1.26/0.98  ------ Abstraction refinement Options
% 1.26/0.98  
% 1.26/0.98  --abstr_ref                             []
% 1.26/0.98  --abstr_ref_prep                        false
% 1.26/0.98  --abstr_ref_until_sat                   false
% 1.26/0.98  --abstr_ref_sig_restrict                funpre
% 1.26/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.26/0.98  --abstr_ref_under                       []
% 1.26/0.98  
% 1.26/0.98  ------ SAT Options
% 1.26/0.98  
% 1.26/0.98  --sat_mode                              false
% 1.26/0.98  --sat_fm_restart_options                ""
% 1.26/0.98  --sat_gr_def                            false
% 1.26/0.98  --sat_epr_types                         true
% 1.26/0.98  --sat_non_cyclic_types                  false
% 1.26/0.98  --sat_finite_models                     false
% 1.26/0.98  --sat_fm_lemmas                         false
% 1.26/0.98  --sat_fm_prep                           false
% 1.26/0.98  --sat_fm_uc_incr                        true
% 1.26/0.98  --sat_out_model                         small
% 1.26/0.98  --sat_out_clauses                       false
% 1.26/0.98  
% 1.26/0.98  ------ QBF Options
% 1.26/0.98  
% 1.26/0.98  --qbf_mode                              false
% 1.26/0.98  --qbf_elim_univ                         false
% 1.26/0.98  --qbf_dom_inst                          none
% 1.26/0.98  --qbf_dom_pre_inst                      false
% 1.26/0.98  --qbf_sk_in                             false
% 1.26/0.98  --qbf_pred_elim                         true
% 1.26/0.98  --qbf_split                             512
% 1.26/0.98  
% 1.26/0.98  ------ BMC1 Options
% 1.26/0.98  
% 1.26/0.98  --bmc1_incremental                      false
% 1.26/0.98  --bmc1_axioms                           reachable_all
% 1.26/0.98  --bmc1_min_bound                        0
% 1.26/0.98  --bmc1_max_bound                        -1
% 1.26/0.98  --bmc1_max_bound_default                -1
% 1.26/0.98  --bmc1_symbol_reachability              true
% 1.26/0.98  --bmc1_property_lemmas                  false
% 1.26/0.98  --bmc1_k_induction                      false
% 1.26/0.98  --bmc1_non_equiv_states                 false
% 1.26/0.98  --bmc1_deadlock                         false
% 1.26/0.98  --bmc1_ucm                              false
% 1.26/0.98  --bmc1_add_unsat_core                   none
% 1.26/0.98  --bmc1_unsat_core_children              false
% 1.26/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.26/0.98  --bmc1_out_stat                         full
% 1.26/0.98  --bmc1_ground_init                      false
% 1.26/0.98  --bmc1_pre_inst_next_state              false
% 1.26/0.98  --bmc1_pre_inst_state                   false
% 1.26/0.98  --bmc1_pre_inst_reach_state             false
% 1.26/0.98  --bmc1_out_unsat_core                   false
% 1.26/0.98  --bmc1_aig_witness_out                  false
% 1.26/0.98  --bmc1_verbose                          false
% 1.26/0.98  --bmc1_dump_clauses_tptp                false
% 1.26/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.26/0.98  --bmc1_dump_file                        -
% 1.26/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.26/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.26/0.98  --bmc1_ucm_extend_mode                  1
% 1.26/0.98  --bmc1_ucm_init_mode                    2
% 1.26/0.98  --bmc1_ucm_cone_mode                    none
% 1.26/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.26/0.98  --bmc1_ucm_relax_model                  4
% 1.26/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.26/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.26/0.98  --bmc1_ucm_layered_model                none
% 1.26/0.98  --bmc1_ucm_max_lemma_size               10
% 1.26/0.98  
% 1.26/0.98  ------ AIG Options
% 1.26/0.98  
% 1.26/0.98  --aig_mode                              false
% 1.26/0.98  
% 1.26/0.98  ------ Instantiation Options
% 1.26/0.98  
% 1.26/0.98  --instantiation_flag                    true
% 1.26/0.98  --inst_sos_flag                         false
% 1.26/0.98  --inst_sos_phase                        true
% 1.26/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.26/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.26/0.98  --inst_lit_sel_side                     none
% 1.26/0.98  --inst_solver_per_active                1400
% 1.26/0.98  --inst_solver_calls_frac                1.
% 1.26/0.98  --inst_passive_queue_type               priority_queues
% 1.26/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.26/0.98  --inst_passive_queues_freq              [25;2]
% 1.26/0.98  --inst_dismatching                      true
% 1.26/0.98  --inst_eager_unprocessed_to_passive     true
% 1.26/0.98  --inst_prop_sim_given                   true
% 1.26/0.98  --inst_prop_sim_new                     false
% 1.26/0.98  --inst_subs_new                         false
% 1.26/0.98  --inst_eq_res_simp                      false
% 1.26/0.98  --inst_subs_given                       false
% 1.26/0.98  --inst_orphan_elimination               true
% 1.26/0.98  --inst_learning_loop_flag               true
% 1.26/0.98  --inst_learning_start                   3000
% 1.26/0.98  --inst_learning_factor                  2
% 1.26/0.98  --inst_start_prop_sim_after_learn       3
% 1.26/0.98  --inst_sel_renew                        solver
% 1.26/0.98  --inst_lit_activity_flag                true
% 1.26/0.98  --inst_restr_to_given                   false
% 1.26/0.98  --inst_activity_threshold               500
% 1.26/0.98  --inst_out_proof                        true
% 1.26/0.98  
% 1.26/0.98  ------ Resolution Options
% 1.26/0.98  
% 1.26/0.98  --resolution_flag                       false
% 1.26/0.98  --res_lit_sel                           adaptive
% 1.26/0.98  --res_lit_sel_side                      none
% 1.26/0.98  --res_ordering                          kbo
% 1.26/0.98  --res_to_prop_solver                    active
% 1.26/0.98  --res_prop_simpl_new                    false
% 1.26/0.98  --res_prop_simpl_given                  true
% 1.26/0.98  --res_passive_queue_type                priority_queues
% 1.26/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.26/0.98  --res_passive_queues_freq               [15;5]
% 1.26/0.98  --res_forward_subs                      full
% 1.26/0.98  --res_backward_subs                     full
% 1.26/0.98  --res_forward_subs_resolution           true
% 1.26/0.98  --res_backward_subs_resolution          true
% 1.26/0.98  --res_orphan_elimination                true
% 1.26/0.98  --res_time_limit                        2.
% 1.26/0.98  --res_out_proof                         true
% 1.26/0.98  
% 1.26/0.98  ------ Superposition Options
% 1.26/0.98  
% 1.26/0.98  --superposition_flag                    true
% 1.26/0.98  --sup_passive_queue_type                priority_queues
% 1.26/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.26/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.26/0.98  --demod_completeness_check              fast
% 1.26/0.98  --demod_use_ground                      true
% 1.26/0.98  --sup_to_prop_solver                    passive
% 1.26/0.98  --sup_prop_simpl_new                    true
% 1.26/0.98  --sup_prop_simpl_given                  true
% 1.26/0.98  --sup_fun_splitting                     false
% 1.26/0.98  --sup_smt_interval                      50000
% 1.26/0.98  
% 1.26/0.98  ------ Superposition Simplification Setup
% 1.26/0.98  
% 1.26/0.98  --sup_indices_passive                   []
% 1.26/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.26/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.26/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.26/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.26/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.26/0.98  --sup_full_bw                           [BwDemod]
% 1.26/0.98  --sup_immed_triv                        [TrivRules]
% 1.26/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.26/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.26/0.98  --sup_immed_bw_main                     []
% 1.26/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.26/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.26/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.26/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.26/0.98  
% 1.26/0.98  ------ Combination Options
% 1.26/0.98  
% 1.26/0.98  --comb_res_mult                         3
% 1.26/0.98  --comb_sup_mult                         2
% 1.26/0.98  --comb_inst_mult                        10
% 1.26/0.98  
% 1.26/0.98  ------ Debug Options
% 1.26/0.98  
% 1.26/0.98  --dbg_backtrace                         false
% 1.26/0.98  --dbg_dump_prop_clauses                 false
% 1.26/0.98  --dbg_dump_prop_clauses_file            -
% 1.26/0.98  --dbg_out_stat                          false
% 1.26/0.98  
% 1.26/0.98  
% 1.26/0.98  
% 1.26/0.98  
% 1.26/0.98  ------ Proving...
% 1.26/0.98  
% 1.26/0.98  
% 1.26/0.98  % SZS status Theorem for theBenchmark.p
% 1.26/0.98  
% 1.26/0.98   Resolution empty clause
% 1.26/0.98  
% 1.26/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.26/0.98  
% 1.26/0.98  fof(f9,axiom,(
% 1.26/0.98    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ? [X2] : m2_orders_2(X2,X0,X1))),
% 1.26/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.26/0.98  
% 1.26/0.98  fof(f22,plain,(
% 1.26/0.98    ! [X0,X1] : (? [X2] : m2_orders_2(X2,X0,X1) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.26/0.98    inference(ennf_transformation,[],[f9])).
% 1.26/0.98  
% 1.26/0.98  fof(f23,plain,(
% 1.26/0.98    ! [X0,X1] : (? [X2] : m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.26/0.98    inference(flattening,[],[f22])).
% 1.26/0.98  
% 1.26/0.98  fof(f38,plain,(
% 1.26/0.98    ! [X1,X0] : (? [X2] : m2_orders_2(X2,X0,X1) => m2_orders_2(sK3(X0,X1),X0,X1))),
% 1.26/0.98    introduced(choice_axiom,[])).
% 1.26/0.98  
% 1.26/0.98  fof(f39,plain,(
% 1.26/0.98    ! [X0,X1] : (m2_orders_2(sK3(X0,X1),X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.26/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f38])).
% 1.26/0.98  
% 1.26/0.98  fof(f55,plain,(
% 1.26/0.98    ( ! [X0,X1] : (m2_orders_2(sK3(X0,X1),X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.26/0.98    inference(cnf_transformation,[],[f39])).
% 1.26/0.98  
% 1.26/0.98  fof(f12,conjecture,(
% 1.26/0.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 1.26/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.26/0.98  
% 1.26/0.98  fof(f13,negated_conjecture,(
% 1.26/0.98    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 1.26/0.98    inference(negated_conjecture,[],[f12])).
% 1.26/0.98  
% 1.26/0.98  fof(f28,plain,(
% 1.26/0.98    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.26/0.98    inference(ennf_transformation,[],[f13])).
% 1.26/0.98  
% 1.26/0.98  fof(f29,plain,(
% 1.26/0.98    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.26/0.98    inference(flattening,[],[f28])).
% 1.26/0.98  
% 1.26/0.98  fof(f41,plain,(
% 1.26/0.98    ( ! [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) => (k1_xboole_0 = k3_tarski(k4_orders_2(X0,sK5)) & m1_orders_1(sK5,k1_orders_1(u1_struct_0(X0))))) )),
% 1.26/0.98    introduced(choice_axiom,[])).
% 1.26/0.98  
% 1.26/0.98  fof(f40,plain,(
% 1.26/0.98    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(sK4,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK4)))) & l1_orders_2(sK4) & v5_orders_2(sK4) & v4_orders_2(sK4) & v3_orders_2(sK4) & ~v2_struct_0(sK4))),
% 1.26/0.98    introduced(choice_axiom,[])).
% 1.26/0.98  
% 1.26/0.98  fof(f42,plain,(
% 1.26/0.98    (k1_xboole_0 = k3_tarski(k4_orders_2(sK4,sK5)) & m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4)))) & l1_orders_2(sK4) & v5_orders_2(sK4) & v4_orders_2(sK4) & v3_orders_2(sK4) & ~v2_struct_0(sK4)),
% 1.26/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f29,f41,f40])).
% 1.26/0.98  
% 1.26/0.98  fof(f63,plain,(
% 1.26/0.98    m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4)))),
% 1.26/0.98    inference(cnf_transformation,[],[f42])).
% 1.26/0.98  
% 1.26/0.98  fof(f62,plain,(
% 1.26/0.98    l1_orders_2(sK4)),
% 1.26/0.98    inference(cnf_transformation,[],[f42])).
% 1.26/0.98  
% 1.26/0.98  fof(f58,plain,(
% 1.26/0.98    ~v2_struct_0(sK4)),
% 1.26/0.98    inference(cnf_transformation,[],[f42])).
% 1.26/0.98  
% 1.26/0.98  fof(f59,plain,(
% 1.26/0.98    v3_orders_2(sK4)),
% 1.26/0.98    inference(cnf_transformation,[],[f42])).
% 1.26/0.98  
% 1.26/0.98  fof(f60,plain,(
% 1.26/0.98    v4_orders_2(sK4)),
% 1.26/0.98    inference(cnf_transformation,[],[f42])).
% 1.26/0.98  
% 1.26/0.98  fof(f61,plain,(
% 1.26/0.98    v5_orders_2(sK4)),
% 1.26/0.98    inference(cnf_transformation,[],[f42])).
% 1.26/0.98  
% 1.26/0.98  fof(f8,axiom,(
% 1.26/0.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1)))))),
% 1.26/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.26/0.98  
% 1.26/0.98  fof(f20,plain,(
% 1.26/0.98    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.26/0.98    inference(ennf_transformation,[],[f8])).
% 1.26/0.98  
% 1.26/0.98  fof(f21,plain,(
% 1.26/0.98    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.26/0.98    inference(flattening,[],[f20])).
% 1.26/0.98  
% 1.26/0.98  fof(f34,plain,(
% 1.26/0.98    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~m2_orders_2(X3,X0,X1)) & (m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.26/0.98    inference(nnf_transformation,[],[f21])).
% 1.26/0.98  
% 1.26/0.98  fof(f35,plain,(
% 1.26/0.98    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.26/0.98    inference(rectify,[],[f34])).
% 1.26/0.98  
% 1.26/0.98  fof(f36,plain,(
% 1.26/0.98    ! [X2,X1,X0] : (? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2))) => ((~m2_orders_2(sK2(X0,X1,X2),X0,X1) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (m2_orders_2(sK2(X0,X1,X2),X0,X1) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.26/0.98    introduced(choice_axiom,[])).
% 1.26/0.98  
% 1.26/0.98  fof(f37,plain,(
% 1.26/0.98    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ((~m2_orders_2(sK2(X0,X1,X2),X0,X1) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (m2_orders_2(sK2(X0,X1,X2),X0,X1) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.26/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).
% 1.26/0.98  
% 1.26/0.98  fof(f52,plain,(
% 1.26/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1) | k4_orders_2(X0,X1) != X2 | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.26/0.98    inference(cnf_transformation,[],[f37])).
% 1.26/0.98  
% 1.26/0.98  fof(f65,plain,(
% 1.26/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_orders_2(X0,X1)) | ~m2_orders_2(X4,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.26/0.98    inference(equality_resolution,[],[f52])).
% 1.26/0.98  
% 1.26/0.98  fof(f64,plain,(
% 1.26/0.98    k1_xboole_0 = k3_tarski(k4_orders_2(sK4,sK5))),
% 1.26/0.98    inference(cnf_transformation,[],[f42])).
% 1.26/0.98  
% 1.26/0.98  fof(f3,axiom,(
% 1.26/0.98    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.26/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.26/0.98  
% 1.26/0.98  fof(f16,plain,(
% 1.26/0.98    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.26/0.98    inference(ennf_transformation,[],[f3])).
% 1.26/0.98  
% 1.26/0.98  fof(f45,plain,(
% 1.26/0.98    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 1.26/0.98    inference(cnf_transformation,[],[f16])).
% 1.26/0.98  
% 1.26/0.98  fof(f4,axiom,(
% 1.26/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 1.26/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.26/0.98  
% 1.26/0.98  fof(f17,plain,(
% 1.26/0.98    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 1.26/0.98    inference(ennf_transformation,[],[f4])).
% 1.26/0.98  
% 1.26/0.98  fof(f46,plain,(
% 1.26/0.98    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 1.26/0.98    inference(cnf_transformation,[],[f17])).
% 1.26/0.98  
% 1.26/0.98  fof(f6,axiom,(
% 1.26/0.98    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_xboole_0(X2,X1)) => r1_xboole_0(k3_tarski(X0),X1))),
% 1.26/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.26/0.98  
% 1.26/0.98  fof(f18,plain,(
% 1.26/0.98    ! [X0,X1] : (r1_xboole_0(k3_tarski(X0),X1) | ? [X2] : (~r1_xboole_0(X2,X1) & r2_hidden(X2,X0)))),
% 1.26/0.98    inference(ennf_transformation,[],[f6])).
% 1.26/0.98  
% 1.26/0.98  fof(f32,plain,(
% 1.26/0.98    ! [X1,X0] : (? [X2] : (~r1_xboole_0(X2,X1) & r2_hidden(X2,X0)) => (~r1_xboole_0(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 1.26/0.98    introduced(choice_axiom,[])).
% 1.26/0.98  
% 1.26/0.98  fof(f33,plain,(
% 1.26/0.98    ! [X0,X1] : (r1_xboole_0(k3_tarski(X0),X1) | (~r1_xboole_0(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 1.26/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f32])).
% 1.26/0.98  
% 1.26/0.98  fof(f48,plain,(
% 1.26/0.98    ( ! [X0,X1] : (r1_xboole_0(k3_tarski(X0),X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 1.26/0.98    inference(cnf_transformation,[],[f33])).
% 1.26/0.98  
% 1.26/0.98  fof(f2,axiom,(
% 1.26/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.26/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.26/0.98  
% 1.26/0.98  fof(f44,plain,(
% 1.26/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.26/0.98    inference(cnf_transformation,[],[f2])).
% 1.26/0.98  
% 1.26/0.98  fof(f7,axiom,(
% 1.26/0.98    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.26/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.26/0.98  
% 1.26/0.98  fof(f19,plain,(
% 1.26/0.98    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.26/0.98    inference(ennf_transformation,[],[f7])).
% 1.26/0.98  
% 1.26/0.98  fof(f50,plain,(
% 1.26/0.98    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.26/0.98    inference(cnf_transformation,[],[f19])).
% 1.26/0.98  
% 1.26/0.98  fof(f5,axiom,(
% 1.26/0.98    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.26/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.26/0.98  
% 1.26/0.98  fof(f47,plain,(
% 1.26/0.98    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.26/0.98    inference(cnf_transformation,[],[f5])).
% 1.26/0.98  
% 1.26/0.98  fof(f1,axiom,(
% 1.26/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.26/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.26/0.98  
% 1.26/0.98  fof(f14,plain,(
% 1.26/0.98    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 1.26/0.98    inference(unused_predicate_definition_removal,[],[f1])).
% 1.26/0.98  
% 1.26/0.98  fof(f15,plain,(
% 1.26/0.98    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 1.26/0.98    inference(ennf_transformation,[],[f14])).
% 1.26/0.98  
% 1.26/0.98  fof(f30,plain,(
% 1.26/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.26/0.98    introduced(choice_axiom,[])).
% 1.26/0.98  
% 1.26/0.98  fof(f31,plain,(
% 1.26/0.98    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0))),
% 1.26/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f30])).
% 1.26/0.98  
% 1.26/0.98  fof(f43,plain,(
% 1.26/0.98    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 1.26/0.98    inference(cnf_transformation,[],[f31])).
% 1.26/0.98  
% 1.26/0.98  fof(f10,axiom,(
% 1.26/0.98    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k4_orders_2(X0,X1)))),
% 1.26/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.26/0.98  
% 1.26/0.98  fof(f24,plain,(
% 1.26/0.98    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.26/0.98    inference(ennf_transformation,[],[f10])).
% 1.26/0.98  
% 1.26/0.98  fof(f25,plain,(
% 1.26/0.98    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.26/0.98    inference(flattening,[],[f24])).
% 1.26/0.98  
% 1.26/0.98  fof(f56,plain,(
% 1.26/0.98    ( ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.26/0.98    inference(cnf_transformation,[],[f25])).
% 1.26/0.98  
% 1.26/0.98  fof(f51,plain,(
% 1.26/0.98    ( ! [X4,X2,X0,X1] : (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2) | k4_orders_2(X0,X1) != X2 | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.26/0.98    inference(cnf_transformation,[],[f37])).
% 1.26/0.98  
% 1.26/0.98  fof(f66,plain,(
% 1.26/0.98    ( ! [X4,X0,X1] : (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.26/0.98    inference(equality_resolution,[],[f51])).
% 1.26/0.98  
% 1.26/0.98  fof(f11,axiom,(
% 1.26/0.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => ~r1_xboole_0(X2,X3)))))),
% 1.26/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.26/0.98  
% 1.26/0.98  fof(f26,plain,(
% 1.26/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.26/0.98    inference(ennf_transformation,[],[f11])).
% 1.26/0.98  
% 1.26/0.98  fof(f27,plain,(
% 1.26/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.26/0.98    inference(flattening,[],[f26])).
% 1.26/0.98  
% 1.26/0.98  fof(f57,plain,(
% 1.26/0.98    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.26/0.98    inference(cnf_transformation,[],[f27])).
% 1.26/0.98  
% 1.26/0.98  cnf(c_12,plain,
% 1.26/0.98      ( m2_orders_2(sK3(X0,X1),X0,X1)
% 1.26/0.98      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
% 1.26/0.98      | v2_struct_0(X0)
% 1.26/0.98      | ~ v3_orders_2(X0)
% 1.26/0.98      | ~ v4_orders_2(X0)
% 1.26/0.98      | ~ v5_orders_2(X0)
% 1.26/0.98      | ~ l1_orders_2(X0) ),
% 1.26/0.98      inference(cnf_transformation,[],[f55]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_16,negated_conjecture,
% 1.26/0.98      ( m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4))) ),
% 1.26/0.98      inference(cnf_transformation,[],[f63]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_315,plain,
% 1.26/0.98      ( m2_orders_2(sK3(X0,X1),X0,X1)
% 1.26/0.98      | v2_struct_0(X0)
% 1.26/0.98      | ~ v3_orders_2(X0)
% 1.26/0.98      | ~ v4_orders_2(X0)
% 1.26/0.98      | ~ v5_orders_2(X0)
% 1.26/0.98      | ~ l1_orders_2(X0)
% 1.26/0.98      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK4))
% 1.26/0.98      | sK5 != X1 ),
% 1.26/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_16]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_316,plain,
% 1.26/0.98      ( m2_orders_2(sK3(X0,sK5),X0,sK5)
% 1.26/0.98      | v2_struct_0(X0)
% 1.26/0.98      | ~ v3_orders_2(X0)
% 1.26/0.98      | ~ v4_orders_2(X0)
% 1.26/0.98      | ~ v5_orders_2(X0)
% 1.26/0.98      | ~ l1_orders_2(X0)
% 1.26/0.98      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK4)) ),
% 1.26/0.98      inference(unflattening,[status(thm)],[c_315]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_17,negated_conjecture,
% 1.26/0.98      ( l1_orders_2(sK4) ),
% 1.26/0.98      inference(cnf_transformation,[],[f62]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_688,plain,
% 1.26/0.98      ( m2_orders_2(sK3(X0,sK5),X0,sK5)
% 1.26/0.98      | v2_struct_0(X0)
% 1.26/0.98      | ~ v3_orders_2(X0)
% 1.26/0.98      | ~ v4_orders_2(X0)
% 1.26/0.98      | ~ v5_orders_2(X0)
% 1.26/0.98      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK4))
% 1.26/0.98      | sK4 != X0 ),
% 1.26/0.98      inference(resolution_lifted,[status(thm)],[c_316,c_17]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_689,plain,
% 1.26/0.98      ( m2_orders_2(sK3(sK4,sK5),sK4,sK5)
% 1.26/0.98      | v2_struct_0(sK4)
% 1.26/0.98      | ~ v3_orders_2(sK4)
% 1.26/0.98      | ~ v4_orders_2(sK4)
% 1.26/0.98      | ~ v5_orders_2(sK4)
% 1.26/0.98      | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4)) ),
% 1.26/0.98      inference(unflattening,[status(thm)],[c_688]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_21,negated_conjecture,
% 1.26/0.98      ( ~ v2_struct_0(sK4) ),
% 1.26/0.98      inference(cnf_transformation,[],[f58]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_20,negated_conjecture,
% 1.26/0.98      ( v3_orders_2(sK4) ),
% 1.26/0.98      inference(cnf_transformation,[],[f59]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_19,negated_conjecture,
% 1.26/0.98      ( v4_orders_2(sK4) ),
% 1.26/0.98      inference(cnf_transformation,[],[f60]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_18,negated_conjecture,
% 1.26/0.98      ( v5_orders_2(sK4) ),
% 1.26/0.98      inference(cnf_transformation,[],[f61]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_691,plain,
% 1.26/0.98      ( m2_orders_2(sK3(sK4,sK5),sK4,sK5)
% 1.26/0.98      | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4)) ),
% 1.26/0.98      inference(global_propositional_subsumption,
% 1.26/0.98                [status(thm)],
% 1.26/0.98                [c_689,c_21,c_20,c_19,c_18]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_831,plain,
% 1.26/0.98      ( m2_orders_2(sK3(sK4,sK5),sK4,sK5) ),
% 1.26/0.98      inference(equality_resolution_simp,[status(thm)],[c_691]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_1276,plain,
% 1.26/0.98      ( m2_orders_2(sK3(sK4,sK5),sK4,sK5) = iProver_top ),
% 1.26/0.98      inference(predicate_to_equality,[status(thm)],[c_831]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_10,plain,
% 1.26/0.98      ( ~ m2_orders_2(X0,X1,X2)
% 1.26/0.98      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.26/0.98      | r2_hidden(X0,k4_orders_2(X1,X2))
% 1.26/0.98      | v2_struct_0(X1)
% 1.26/0.98      | ~ v3_orders_2(X1)
% 1.26/0.98      | ~ v4_orders_2(X1)
% 1.26/0.98      | ~ v5_orders_2(X1)
% 1.26/0.98      | ~ l1_orders_2(X1) ),
% 1.26/0.98      inference(cnf_transformation,[],[f65]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_471,plain,
% 1.26/0.98      ( ~ m2_orders_2(X0,X1,X2)
% 1.26/0.98      | r2_hidden(X0,k4_orders_2(X1,X2))
% 1.26/0.98      | v2_struct_0(X1)
% 1.26/0.98      | ~ v3_orders_2(X1)
% 1.26/0.98      | ~ v4_orders_2(X1)
% 1.26/0.98      | ~ v5_orders_2(X1)
% 1.26/0.98      | ~ l1_orders_2(X1)
% 1.26/0.98      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK4))
% 1.26/0.98      | sK5 != X2 ),
% 1.26/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_16]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_472,plain,
% 1.26/0.98      ( ~ m2_orders_2(X0,X1,sK5)
% 1.26/0.98      | r2_hidden(X0,k4_orders_2(X1,sK5))
% 1.26/0.98      | v2_struct_0(X1)
% 1.26/0.98      | ~ v3_orders_2(X1)
% 1.26/0.98      | ~ v4_orders_2(X1)
% 1.26/0.98      | ~ v5_orders_2(X1)
% 1.26/0.98      | ~ l1_orders_2(X1)
% 1.26/0.98      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK4)) ),
% 1.26/0.98      inference(unflattening,[status(thm)],[c_471]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_702,plain,
% 1.26/0.98      ( ~ m2_orders_2(X0,X1,sK5)
% 1.26/0.98      | r2_hidden(X0,k4_orders_2(X1,sK5))
% 1.26/0.98      | v2_struct_0(X1)
% 1.26/0.98      | ~ v3_orders_2(X1)
% 1.26/0.98      | ~ v4_orders_2(X1)
% 1.26/0.98      | ~ v5_orders_2(X1)
% 1.26/0.98      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK4))
% 1.26/0.98      | sK4 != X1 ),
% 1.26/0.98      inference(resolution_lifted,[status(thm)],[c_472,c_17]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_703,plain,
% 1.26/0.98      ( ~ m2_orders_2(X0,sK4,sK5)
% 1.26/0.98      | r2_hidden(X0,k4_orders_2(sK4,sK5))
% 1.26/0.98      | v2_struct_0(sK4)
% 1.26/0.98      | ~ v3_orders_2(sK4)
% 1.26/0.98      | ~ v4_orders_2(sK4)
% 1.26/0.98      | ~ v5_orders_2(sK4)
% 1.26/0.98      | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4)) ),
% 1.26/0.98      inference(unflattening,[status(thm)],[c_702]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_707,plain,
% 1.26/0.98      ( ~ m2_orders_2(X0,sK4,sK5)
% 1.26/0.98      | r2_hidden(X0,k4_orders_2(sK4,sK5))
% 1.26/0.98      | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4)) ),
% 1.26/0.98      inference(global_propositional_subsumption,
% 1.26/0.98                [status(thm)],
% 1.26/0.98                [c_703,c_21,c_20,c_19,c_18]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_827,plain,
% 1.26/0.98      ( ~ m2_orders_2(X0,sK4,sK5) | r2_hidden(X0,k4_orders_2(sK4,sK5)) ),
% 1.26/0.98      inference(equality_resolution_simp,[status(thm)],[c_707]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_865,plain,
% 1.26/0.98      ( ~ m2_orders_2(X0,sK4,sK5) | r2_hidden(X0,k4_orders_2(sK4,sK5)) ),
% 1.26/0.98      inference(prop_impl,[status(thm)],[c_827]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_1277,plain,
% 1.26/0.98      ( m2_orders_2(X0,sK4,sK5) != iProver_top
% 1.26/0.98      | r2_hidden(X0,k4_orders_2(sK4,sK5)) = iProver_top ),
% 1.26/0.98      inference(predicate_to_equality,[status(thm)],[c_865]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_15,negated_conjecture,
% 1.26/0.98      ( k1_xboole_0 = k3_tarski(k4_orders_2(sK4,sK5)) ),
% 1.26/0.98      inference(cnf_transformation,[],[f64]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_2,plain,
% 1.26/0.98      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 1.26/0.98      inference(cnf_transformation,[],[f45]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_3,plain,
% 1.26/0.98      ( r1_tarski(X0,k3_tarski(X1)) | ~ r2_hidden(X0,X1) ),
% 1.26/0.98      inference(cnf_transformation,[],[f46]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_245,plain,
% 1.26/0.98      ( ~ r2_hidden(X0,X1)
% 1.26/0.98      | X0 != X2
% 1.26/0.98      | k3_tarski(X1) != k1_xboole_0
% 1.26/0.98      | k1_xboole_0 = X2 ),
% 1.26/0.98      inference(resolution_lifted,[status(thm)],[c_2,c_3]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_246,plain,
% 1.26/0.98      ( ~ r2_hidden(X0,X1) | k3_tarski(X1) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 1.26/0.98      inference(unflattening,[status(thm)],[c_245]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_1282,plain,
% 1.26/0.98      ( k3_tarski(X0) != k1_xboole_0
% 1.26/0.98      | k1_xboole_0 = X1
% 1.26/0.98      | r2_hidden(X1,X0) != iProver_top ),
% 1.26/0.98      inference(predicate_to_equality,[status(thm)],[c_246]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_2509,plain,
% 1.26/0.98      ( k1_xboole_0 = X0 | r2_hidden(X0,k4_orders_2(sK4,sK5)) != iProver_top ),
% 1.26/0.98      inference(superposition,[status(thm)],[c_15,c_1282]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_2587,plain,
% 1.26/0.98      ( k1_xboole_0 = X0 | m2_orders_2(X0,sK4,sK5) != iProver_top ),
% 1.26/0.98      inference(superposition,[status(thm)],[c_1277,c_2509]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_6,plain,
% 1.26/0.98      ( r1_xboole_0(k3_tarski(X0),X1) | r2_hidden(sK1(X0,X1),X0) ),
% 1.26/0.98      inference(cnf_transformation,[],[f48]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_1284,plain,
% 1.26/0.98      ( r1_xboole_0(k3_tarski(X0),X1) = iProver_top
% 1.26/0.98      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 1.26/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_1,plain,
% 1.26/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 1.26/0.98      inference(cnf_transformation,[],[f44]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_7,plain,
% 1.26/0.98      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 1.26/0.98      inference(cnf_transformation,[],[f50]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_236,plain,
% 1.26/0.98      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 1.26/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_7]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_237,plain,
% 1.26/0.98      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 1.26/0.98      inference(unflattening,[status(thm)],[c_236]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_1283,plain,
% 1.26/0.98      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 1.26/0.98      inference(predicate_to_equality,[status(thm)],[c_237]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_1882,plain,
% 1.26/0.98      ( r1_xboole_0(k3_tarski(k1_xboole_0),X0) = iProver_top ),
% 1.26/0.98      inference(superposition,[status(thm)],[c_1284,c_1283]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_4,plain,
% 1.26/0.98      ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
% 1.26/0.98      inference(cnf_transformation,[],[f47]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_1889,plain,
% 1.26/0.98      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 1.26/0.98      inference(light_normalisation,[status(thm)],[c_1882,c_4]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_0,plain,
% 1.26/0.98      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 1.26/0.98      inference(cnf_transformation,[],[f43]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_13,plain,
% 1.26/0.98      ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(X1)))
% 1.26/0.98      | v2_struct_0(X1)
% 1.26/0.98      | ~ v3_orders_2(X1)
% 1.26/0.98      | ~ v4_orders_2(X1)
% 1.26/0.98      | ~ v5_orders_2(X1)
% 1.26/0.98      | ~ l1_orders_2(X1)
% 1.26/0.98      | ~ v1_xboole_0(k4_orders_2(X1,X0)) ),
% 1.26/0.98      inference(cnf_transformation,[],[f56]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_501,plain,
% 1.26/0.98      ( v2_struct_0(X0)
% 1.26/0.98      | ~ v3_orders_2(X0)
% 1.26/0.98      | ~ v4_orders_2(X0)
% 1.26/0.98      | ~ v5_orders_2(X0)
% 1.26/0.98      | ~ l1_orders_2(X0)
% 1.26/0.98      | ~ v1_xboole_0(k4_orders_2(X0,X1))
% 1.26/0.98      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK4))
% 1.26/0.98      | sK5 != X1 ),
% 1.26/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_16]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_502,plain,
% 1.26/0.98      ( v2_struct_0(X0)
% 1.26/0.98      | ~ v3_orders_2(X0)
% 1.26/0.98      | ~ v4_orders_2(X0)
% 1.26/0.98      | ~ v5_orders_2(X0)
% 1.26/0.98      | ~ l1_orders_2(X0)
% 1.26/0.98      | ~ v1_xboole_0(k4_orders_2(X0,sK5))
% 1.26/0.98      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK4)) ),
% 1.26/0.98      inference(unflattening,[status(thm)],[c_501]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_626,plain,
% 1.26/0.98      ( v2_struct_0(X0)
% 1.26/0.98      | ~ v3_orders_2(X0)
% 1.26/0.98      | ~ v4_orders_2(X0)
% 1.26/0.98      | ~ v5_orders_2(X0)
% 1.26/0.98      | ~ v1_xboole_0(k4_orders_2(X0,sK5))
% 1.26/0.98      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK4))
% 1.26/0.98      | sK4 != X0 ),
% 1.26/0.98      inference(resolution_lifted,[status(thm)],[c_502,c_17]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_627,plain,
% 1.26/0.98      ( v2_struct_0(sK4)
% 1.26/0.98      | ~ v3_orders_2(sK4)
% 1.26/0.98      | ~ v4_orders_2(sK4)
% 1.26/0.98      | ~ v5_orders_2(sK4)
% 1.26/0.98      | ~ v1_xboole_0(k4_orders_2(sK4,sK5))
% 1.26/0.98      | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4)) ),
% 1.26/0.98      inference(unflattening,[status(thm)],[c_626]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_629,plain,
% 1.26/0.98      ( ~ v1_xboole_0(k4_orders_2(sK4,sK5))
% 1.26/0.98      | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4)) ),
% 1.26/0.98      inference(global_propositional_subsumption,
% 1.26/0.98                [status(thm)],
% 1.26/0.98                [c_627,c_21,c_20,c_19,c_18]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_797,plain,
% 1.26/0.98      ( r2_hidden(sK0(X0),X0)
% 1.26/0.98      | k4_orders_2(sK4,sK5) != X0
% 1.26/0.98      | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4)) ),
% 1.26/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_629]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_798,plain,
% 1.26/0.98      ( r2_hidden(sK0(k4_orders_2(sK4,sK5)),k4_orders_2(sK4,sK5)) ),
% 1.26/0.98      inference(unflattening,[status(thm)],[c_797]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_1280,plain,
% 1.26/0.98      ( r2_hidden(sK0(k4_orders_2(sK4,sK5)),k4_orders_2(sK4,sK5)) = iProver_top ),
% 1.26/0.98      inference(predicate_to_equality,[status(thm)],[c_798]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_2585,plain,
% 1.26/0.98      ( sK0(k4_orders_2(sK4,sK5)) = k1_xboole_0 ),
% 1.26/0.98      inference(superposition,[status(thm)],[c_1280,c_2509]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_11,plain,
% 1.26/0.98      ( m2_orders_2(X0,X1,X2)
% 1.26/0.98      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.26/0.98      | ~ r2_hidden(X0,k4_orders_2(X1,X2))
% 1.26/0.98      | v2_struct_0(X1)
% 1.26/0.98      | ~ v3_orders_2(X1)
% 1.26/0.98      | ~ v4_orders_2(X1)
% 1.26/0.98      | ~ v5_orders_2(X1)
% 1.26/0.98      | ~ l1_orders_2(X1) ),
% 1.26/0.98      inference(cnf_transformation,[],[f66]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_441,plain,
% 1.26/0.98      ( m2_orders_2(X0,X1,X2)
% 1.26/0.98      | ~ r2_hidden(X0,k4_orders_2(X1,X2))
% 1.26/0.98      | v2_struct_0(X1)
% 1.26/0.98      | ~ v3_orders_2(X1)
% 1.26/0.98      | ~ v4_orders_2(X1)
% 1.26/0.98      | ~ v5_orders_2(X1)
% 1.26/0.98      | ~ l1_orders_2(X1)
% 1.26/0.98      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK4))
% 1.26/0.98      | sK5 != X2 ),
% 1.26/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_16]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_442,plain,
% 1.26/0.98      ( m2_orders_2(X0,X1,sK5)
% 1.26/0.98      | ~ r2_hidden(X0,k4_orders_2(X1,sK5))
% 1.26/0.98      | v2_struct_0(X1)
% 1.26/0.98      | ~ v3_orders_2(X1)
% 1.26/0.98      | ~ v4_orders_2(X1)
% 1.26/0.98      | ~ v5_orders_2(X1)
% 1.26/0.98      | ~ l1_orders_2(X1)
% 1.26/0.98      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK4)) ),
% 1.26/0.98      inference(unflattening,[status(thm)],[c_441]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_723,plain,
% 1.26/0.98      ( m2_orders_2(X0,X1,sK5)
% 1.26/0.98      | ~ r2_hidden(X0,k4_orders_2(X1,sK5))
% 1.26/0.98      | v2_struct_0(X1)
% 1.26/0.98      | ~ v3_orders_2(X1)
% 1.26/0.98      | ~ v4_orders_2(X1)
% 1.26/0.98      | ~ v5_orders_2(X1)
% 1.26/0.98      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK4))
% 1.26/0.98      | sK4 != X1 ),
% 1.26/0.98      inference(resolution_lifted,[status(thm)],[c_442,c_17]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_724,plain,
% 1.26/0.98      ( m2_orders_2(X0,sK4,sK5)
% 1.26/0.98      | ~ r2_hidden(X0,k4_orders_2(sK4,sK5))
% 1.26/0.98      | v2_struct_0(sK4)
% 1.26/0.98      | ~ v3_orders_2(sK4)
% 1.26/0.98      | ~ v4_orders_2(sK4)
% 1.26/0.98      | ~ v5_orders_2(sK4)
% 1.26/0.98      | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4)) ),
% 1.26/0.98      inference(unflattening,[status(thm)],[c_723]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_728,plain,
% 1.26/0.98      ( m2_orders_2(X0,sK4,sK5)
% 1.26/0.98      | ~ r2_hidden(X0,k4_orders_2(sK4,sK5))
% 1.26/0.98      | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4)) ),
% 1.26/0.98      inference(global_propositional_subsumption,
% 1.26/0.98                [status(thm)],
% 1.26/0.98                [c_724,c_21,c_20,c_19,c_18]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_823,plain,
% 1.26/0.98      ( m2_orders_2(X0,sK4,sK5) | ~ r2_hidden(X0,k4_orders_2(sK4,sK5)) ),
% 1.26/0.98      inference(equality_resolution_simp,[status(thm)],[c_728]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_863,plain,
% 1.26/0.98      ( m2_orders_2(X0,sK4,sK5) | ~ r2_hidden(X0,k4_orders_2(sK4,sK5)) ),
% 1.26/0.98      inference(prop_impl,[status(thm)],[c_823]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_1278,plain,
% 1.26/0.98      ( m2_orders_2(X0,sK4,sK5) = iProver_top
% 1.26/0.98      | r2_hidden(X0,k4_orders_2(sK4,sK5)) != iProver_top ),
% 1.26/0.98      inference(predicate_to_equality,[status(thm)],[c_863]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_1697,plain,
% 1.26/0.98      ( m2_orders_2(sK0(k4_orders_2(sK4,sK5)),sK4,sK5) = iProver_top ),
% 1.26/0.98      inference(superposition,[status(thm)],[c_1280,c_1278]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_14,plain,
% 1.26/0.98      ( ~ m2_orders_2(X0,X1,X2)
% 1.26/0.98      | ~ m2_orders_2(X3,X1,X2)
% 1.26/0.98      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.26/0.98      | ~ r1_xboole_0(X3,X0)
% 1.26/0.98      | v2_struct_0(X1)
% 1.26/0.98      | ~ v3_orders_2(X1)
% 1.26/0.98      | ~ v4_orders_2(X1)
% 1.26/0.98      | ~ v5_orders_2(X1)
% 1.26/0.98      | ~ l1_orders_2(X1) ),
% 1.26/0.98      inference(cnf_transformation,[],[f57]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_408,plain,
% 1.26/0.98      ( ~ m2_orders_2(X0,X1,X2)
% 1.26/0.98      | ~ m2_orders_2(X3,X1,X2)
% 1.26/0.98      | ~ r1_xboole_0(X3,X0)
% 1.26/0.98      | v2_struct_0(X1)
% 1.26/0.98      | ~ v3_orders_2(X1)
% 1.26/0.98      | ~ v4_orders_2(X1)
% 1.26/0.98      | ~ v5_orders_2(X1)
% 1.26/0.98      | ~ l1_orders_2(X1)
% 1.26/0.98      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK4))
% 1.26/0.98      | sK5 != X2 ),
% 1.26/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_16]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_409,plain,
% 1.26/0.98      ( ~ m2_orders_2(X0,X1,sK5)
% 1.26/0.98      | ~ m2_orders_2(X2,X1,sK5)
% 1.26/0.98      | ~ r1_xboole_0(X0,X2)
% 1.26/0.98      | v2_struct_0(X1)
% 1.26/0.98      | ~ v3_orders_2(X1)
% 1.26/0.98      | ~ v4_orders_2(X1)
% 1.26/0.98      | ~ v5_orders_2(X1)
% 1.26/0.98      | ~ l1_orders_2(X1)
% 1.26/0.98      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK4)) ),
% 1.26/0.98      inference(unflattening,[status(thm)],[c_408]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_744,plain,
% 1.26/0.98      ( ~ m2_orders_2(X0,X1,sK5)
% 1.26/0.98      | ~ m2_orders_2(X2,X1,sK5)
% 1.26/0.98      | ~ r1_xboole_0(X0,X2)
% 1.26/0.98      | v2_struct_0(X1)
% 1.26/0.98      | ~ v3_orders_2(X1)
% 1.26/0.98      | ~ v4_orders_2(X1)
% 1.26/0.98      | ~ v5_orders_2(X1)
% 1.26/0.98      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK4))
% 1.26/0.98      | sK4 != X1 ),
% 1.26/0.98      inference(resolution_lifted,[status(thm)],[c_409,c_17]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_745,plain,
% 1.26/0.98      ( ~ m2_orders_2(X0,sK4,sK5)
% 1.26/0.98      | ~ m2_orders_2(X1,sK4,sK5)
% 1.26/0.98      | ~ r1_xboole_0(X0,X1)
% 1.26/0.98      | v2_struct_0(sK4)
% 1.26/0.98      | ~ v3_orders_2(sK4)
% 1.26/0.98      | ~ v4_orders_2(sK4)
% 1.26/0.98      | ~ v5_orders_2(sK4)
% 1.26/0.98      | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4)) ),
% 1.26/0.98      inference(unflattening,[status(thm)],[c_744]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_749,plain,
% 1.26/0.98      ( ~ m2_orders_2(X0,sK4,sK5)
% 1.26/0.98      | ~ m2_orders_2(X1,sK4,sK5)
% 1.26/0.98      | ~ r1_xboole_0(X0,X1)
% 1.26/0.98      | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4)) ),
% 1.26/0.98      inference(global_propositional_subsumption,
% 1.26/0.98                [status(thm)],
% 1.26/0.98                [c_745,c_21,c_20,c_19,c_18]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_819,plain,
% 1.26/0.98      ( ~ m2_orders_2(X0,sK4,sK5)
% 1.26/0.98      | ~ m2_orders_2(X1,sK4,sK5)
% 1.26/0.98      | ~ r1_xboole_0(X0,X1) ),
% 1.26/0.98      inference(equality_resolution_simp,[status(thm)],[c_749]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_1279,plain,
% 1.26/0.98      ( m2_orders_2(X0,sK4,sK5) != iProver_top
% 1.26/0.98      | m2_orders_2(X1,sK4,sK5) != iProver_top
% 1.26/0.98      | r1_xboole_0(X0,X1) != iProver_top ),
% 1.26/0.98      inference(predicate_to_equality,[status(thm)],[c_819]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_1820,plain,
% 1.26/0.98      ( m2_orders_2(X0,sK4,sK5) != iProver_top
% 1.26/0.98      | r1_xboole_0(sK0(k4_orders_2(sK4,sK5)),X0) != iProver_top ),
% 1.26/0.98      inference(superposition,[status(thm)],[c_1697,c_1279]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_2602,plain,
% 1.26/0.98      ( m2_orders_2(X0,sK4,sK5) != iProver_top
% 1.26/0.98      | r1_xboole_0(k1_xboole_0,X0) != iProver_top ),
% 1.26/0.98      inference(demodulation,[status(thm)],[c_2585,c_1820]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_2639,plain,
% 1.26/0.98      ( m2_orders_2(X0,sK4,sK5) != iProver_top ),
% 1.26/0.98      inference(global_propositional_subsumption,
% 1.26/0.98                [status(thm)],
% 1.26/0.98                [c_2587,c_1889,c_2602]) ).
% 1.26/0.98  
% 1.26/0.98  cnf(c_2646,plain,
% 1.26/0.98      ( $false ),
% 1.26/0.98      inference(superposition,[status(thm)],[c_1276,c_2639]) ).
% 1.26/0.98  
% 1.26/0.98  
% 1.26/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 1.26/0.98  
% 1.26/0.98  ------                               Statistics
% 1.26/0.98  
% 1.26/0.98  ------ General
% 1.26/0.98  
% 1.26/0.98  abstr_ref_over_cycles:                  0
% 1.26/0.98  abstr_ref_under_cycles:                 0
% 1.26/0.98  gc_basic_clause_elim:                   0
% 1.26/0.98  forced_gc_time:                         0
% 1.26/0.98  parsing_time:                           0.008
% 1.26/0.98  unif_index_cands_time:                  0.
% 1.26/0.98  unif_index_add_time:                    0.
% 1.26/0.98  orderings_time:                         0.
% 1.26/0.98  out_proof_time:                         0.01
% 1.26/0.98  total_time:                             0.105
% 1.26/0.98  num_of_symbols:                         53
% 1.26/0.98  num_of_terms:                           1766
% 1.26/0.98  
% 1.26/0.98  ------ Preprocessing
% 1.26/0.98  
% 1.26/0.98  num_of_splits:                          0
% 1.26/0.98  num_of_split_atoms:                     0
% 1.26/0.98  num_of_reused_defs:                     0
% 1.26/0.98  num_eq_ax_congr_red:                    19
% 1.26/0.98  num_of_sem_filtered_clauses:            1
% 1.26/0.98  num_of_subtypes:                        0
% 1.26/0.98  monotx_restored_types:                  0
% 1.26/0.98  sat_num_of_epr_types:                   0
% 1.26/0.98  sat_num_of_non_cyclic_types:            0
% 1.26/0.98  sat_guarded_non_collapsed_types:        0
% 1.26/0.98  num_pure_diseq_elim:                    0
% 1.26/0.98  simp_replaced_by:                       0
% 1.26/0.98  res_preprocessed:                       85
% 1.26/0.98  prep_upred:                             0
% 1.26/0.98  prep_unflattend:                        24
% 1.26/0.98  smt_new_axioms:                         0
% 1.26/0.98  pred_elim_cands:                        3
% 1.26/0.98  pred_elim:                              8
% 1.26/0.98  pred_elim_cl:                           8
% 1.26/0.98  pred_elim_cycles:                       12
% 1.26/0.98  merged_defs:                            6
% 1.26/0.98  merged_defs_ncl:                        0
% 1.26/0.98  bin_hyper_res:                          6
% 1.26/0.98  prep_cycles:                            4
% 1.26/0.98  pred_elim_time:                         0.012
% 1.26/0.98  splitting_time:                         0.
% 1.26/0.98  sem_filter_time:                        0.
% 1.26/0.98  monotx_time:                            0.001
% 1.26/0.98  subtype_inf_time:                       0.
% 1.26/0.98  
% 1.26/0.98  ------ Problem properties
% 1.26/0.98  
% 1.26/0.98  clauses:                                14
% 1.26/0.98  conjectures:                            1
% 1.26/0.98  epr:                                    2
% 1.26/0.98  horn:                                   12
% 1.26/0.98  ground:                                 4
% 1.26/0.98  unary:                                  5
% 1.26/0.98  binary:                                 5
% 1.26/0.98  lits:                                   27
% 1.26/0.98  lits_eq:                                6
% 1.26/0.98  fd_pure:                                0
% 1.26/0.98  fd_pseudo:                              0
% 1.26/0.98  fd_cond:                                3
% 1.26/0.98  fd_pseudo_cond:                         0
% 1.26/0.98  ac_symbols:                             0
% 1.26/0.98  
% 1.26/0.98  ------ Propositional Solver
% 1.26/0.98  
% 1.26/0.98  prop_solver_calls:                      28
% 1.26/0.98  prop_fast_solver_calls:                 657
% 1.26/0.98  smt_solver_calls:                       0
% 1.26/0.98  smt_fast_solver_calls:                  0
% 1.26/0.98  prop_num_of_clauses:                    835
% 1.26/0.98  prop_preprocess_simplified:             3132
% 1.26/0.98  prop_fo_subsumed:                       31
% 1.26/0.98  prop_solver_time:                       0.
% 1.26/0.98  smt_solver_time:                        0.
% 1.26/0.98  smt_fast_solver_time:                   0.
% 1.26/0.98  prop_fast_solver_time:                  0.
% 1.26/0.98  prop_unsat_core_time:                   0.
% 1.26/0.98  
% 1.26/0.98  ------ QBF
% 1.26/0.98  
% 1.26/0.98  qbf_q_res:                              0
% 1.26/0.98  qbf_num_tautologies:                    0
% 1.26/0.98  qbf_prep_cycles:                        0
% 1.26/0.98  
% 1.26/0.98  ------ BMC1
% 1.26/0.98  
% 1.26/0.98  bmc1_current_bound:                     -1
% 1.26/0.98  bmc1_last_solved_bound:                 -1
% 1.26/0.98  bmc1_unsat_core_size:                   -1
% 1.26/0.98  bmc1_unsat_core_parents_size:           -1
% 1.26/0.98  bmc1_merge_next_fun:                    0
% 1.26/0.98  bmc1_unsat_core_clauses_time:           0.
% 1.26/0.98  
% 1.26/0.98  ------ Instantiation
% 1.26/0.98  
% 1.26/0.98  inst_num_of_clauses:                    244
% 1.26/0.98  inst_num_in_passive:                    54
% 1.26/0.98  inst_num_in_active:                     157
% 1.26/0.98  inst_num_in_unprocessed:                33
% 1.26/0.98  inst_num_of_loops:                      180
% 1.26/0.98  inst_num_of_learning_restarts:          0
% 1.26/0.98  inst_num_moves_active_passive:          20
% 1.26/0.98  inst_lit_activity:                      0
% 1.26/0.98  inst_lit_activity_moves:                0
% 1.26/0.98  inst_num_tautologies:                   0
% 1.26/0.98  inst_num_prop_implied:                  0
% 1.26/0.98  inst_num_existing_simplified:           0
% 1.26/0.98  inst_num_eq_res_simplified:             0
% 1.26/0.98  inst_num_child_elim:                    0
% 1.26/0.98  inst_num_of_dismatching_blockings:      81
% 1.26/0.98  inst_num_of_non_proper_insts:           246
% 1.26/0.98  inst_num_of_duplicates:                 0
% 1.26/0.98  inst_inst_num_from_inst_to_res:         0
% 1.26/0.98  inst_dismatching_checking_time:         0.
% 1.26/0.98  
% 1.26/0.98  ------ Resolution
% 1.26/0.98  
% 1.26/0.98  res_num_of_clauses:                     0
% 1.26/0.98  res_num_in_passive:                     0
% 1.26/0.98  res_num_in_active:                      0
% 1.26/0.98  res_num_of_loops:                       89
% 1.26/0.98  res_forward_subset_subsumed:            38
% 1.26/0.98  res_backward_subset_subsumed:           2
% 1.26/0.98  res_forward_subsumed:                   0
% 1.26/0.98  res_backward_subsumed:                  0
% 1.26/0.98  res_forward_subsumption_resolution:     0
% 1.26/0.98  res_backward_subsumption_resolution:    0
% 1.26/0.98  res_clause_to_clause_subsumption:       73
% 1.26/0.98  res_orphan_elimination:                 0
% 1.26/0.98  res_tautology_del:                      43
% 1.26/0.98  res_num_eq_res_simplified:              6
% 1.26/0.98  res_num_sel_changes:                    0
% 1.26/0.98  res_moves_from_active_to_pass:          0
% 1.26/0.98  
% 1.26/0.98  ------ Superposition
% 1.26/0.98  
% 1.26/0.98  sup_time_total:                         0.
% 1.26/0.98  sup_time_generating:                    0.
% 1.26/0.98  sup_time_sim_full:                      0.
% 1.26/0.98  sup_time_sim_immed:                     0.
% 1.26/0.98  
% 1.26/0.98  sup_num_of_clauses:                     28
% 1.26/0.98  sup_num_in_active:                      26
% 1.26/0.98  sup_num_in_passive:                     2
% 1.26/0.98  sup_num_of_loops:                       34
% 1.26/0.98  sup_fw_superposition:                   28
% 1.26/0.98  sup_bw_superposition:                   6
% 1.26/0.98  sup_immediate_simplified:               10
% 1.26/0.98  sup_given_eliminated:                   0
% 1.26/0.98  comparisons_done:                       0
% 1.26/0.98  comparisons_avoided:                    0
% 1.26/0.98  
% 1.26/0.98  ------ Simplifications
% 1.26/0.98  
% 1.26/0.98  
% 1.26/0.98  sim_fw_subset_subsumed:                 3
% 1.26/0.98  sim_bw_subset_subsumed:                 6
% 1.26/0.98  sim_fw_subsumed:                        5
% 1.26/0.98  sim_bw_subsumed:                        0
% 1.26/0.98  sim_fw_subsumption_res:                 0
% 1.26/0.98  sim_bw_subsumption_res:                 0
% 1.26/0.98  sim_tautology_del:                      2
% 1.26/0.98  sim_eq_tautology_del:                   3
% 1.26/0.98  sim_eq_res_simp:                        0
% 1.26/0.98  sim_fw_demodulated:                     0
% 1.26/0.98  sim_bw_demodulated:                     4
% 1.26/0.98  sim_light_normalised:                   4
% 1.26/0.98  sim_joinable_taut:                      0
% 1.26/0.98  sim_joinable_simp:                      0
% 1.26/0.98  sim_ac_normalised:                      0
% 1.26/0.98  sim_smt_subsumption:                    0
% 1.26/0.98  
%------------------------------------------------------------------------------
