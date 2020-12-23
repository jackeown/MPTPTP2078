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
% DateTime   : Thu Dec  3 12:12:58 EST 2020

% Result     : Theorem 1.30s
% Output     : CNFRefutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :  154 (1141 expanded)
%              Number of clauses        :   91 ( 303 expanded)
%              Number of leaves         :   18 ( 301 expanded)
%              Depth                    :   23
%              Number of atoms          :  607 (6172 expanded)
%              Number of equality atoms :  132 (1048 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f43,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f23,plain,(
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

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
     => ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,sK5))
        & m1_orders_1(sK5,k1_orders_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
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

fof(f41,plain,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK4,sK5))
    & m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4)))
    & l1_orders_2(sK4)
    & v5_orders_2(sK4)
    & v4_orders_2(sK4)
    & v3_orders_2(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f24,f40,f39])).

fof(f66,plain,(
    k1_xboole_0 = k3_tarski(k4_orders_2(sK4,sK5)) ),
    inference(cnf_transformation,[],[f41])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m2_orders_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
     => m2_orders_2(sK3(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m2_orders_2(sK3(X0,X1),X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f37])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m2_orders_2(sK3(X0,X1),X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f65,plain,(
    m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f60,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f61,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f63,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f18])).

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
    inference(rectify,[],[f33])).

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).

fof(f55,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f69,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_orders_2(X0,X1))
      | ~ m2_orders_2(X4,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f42,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f54,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f70,plain,(
    ! [X4,X0,X1] :
      ( m2_orders_2(X4,X0,X1)
      | ~ r2_hidden(X4,k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_xboole_0(X2,X1) )
     => r1_xboole_0(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_xboole_0(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_xboole_0(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_xboole_0(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ( ~ r1_xboole_0(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f31])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f59,plain,(
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
    inference(cnf_transformation,[],[f22])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1709,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1707,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1706,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2212,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_1707,c_1706])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK4,sK5)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2217,plain,
    ( k3_tarski(k4_orders_2(sK4,sK5)) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2212,c_18])).

cnf(c_8,plain,
    ( r1_tarski(X0,k3_tarski(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1702,plain,
    ( r1_tarski(X0,k3_tarski(X1)) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2629,plain,
    ( r1_tarski(X0,o_0_0_xboole_0) = iProver_top
    | r2_hidden(X0,k4_orders_2(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2217,c_1702])).

cnf(c_2746,plain,
    ( r1_tarski(sK0(k4_orders_2(sK4,sK5)),o_0_0_xboole_0) = iProver_top
    | v1_xboole_0(k4_orders_2(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1709,c_2629])).

cnf(c_16,plain,
    ( m2_orders_2(sK3(X0,X1),X0,X1)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_19,negated_conjecture,
    ( m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_302,plain,
    ( m2_orders_2(sK3(X0,X1),X0,X1)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK4))
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_19])).

cnf(c_303,plain,
    ( m2_orders_2(sK3(X0,sK5),X0,sK5)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_302])).

cnf(c_20,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_592,plain,
    ( m2_orders_2(sK3(X0,sK5),X0,sK5)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK4))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_303,c_20])).

cnf(c_593,plain,
    ( m2_orders_2(sK3(sK4,sK5),sK4,sK5)
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_592])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_23,negated_conjecture,
    ( v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_22,negated_conjecture,
    ( v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_21,negated_conjecture,
    ( v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_595,plain,
    ( m2_orders_2(sK3(sK4,sK5),sK4,sK5)
    | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_593,c_24,c_23,c_22,c_21])).

cnf(c_910,plain,
    ( m2_orders_2(sK3(sK4,sK5),sK4,sK5) ),
    inference(equality_resolution_simp,[status(thm)],[c_595])).

cnf(c_911,plain,
    ( m2_orders_2(sK3(sK4,sK5),sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_910])).

cnf(c_14,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | r2_hidden(X0,k4_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_458,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | r2_hidden(X0,k4_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK4))
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_19])).

cnf(c_459,plain,
    ( ~ m2_orders_2(X0,X1,sK5)
    | r2_hidden(X0,k4_orders_2(X1,sK5))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_458])).

cnf(c_606,plain,
    ( ~ m2_orders_2(X0,X1,sK5)
    | r2_hidden(X0,k4_orders_2(X1,sK5))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK4))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_459,c_20])).

cnf(c_607,plain,
    ( ~ m2_orders_2(X0,sK4,sK5)
    | r2_hidden(X0,k4_orders_2(sK4,sK5))
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_606])).

cnf(c_611,plain,
    ( ~ m2_orders_2(X0,sK4,sK5)
    | r2_hidden(X0,k4_orders_2(sK4,sK5))
    | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_607,c_24,c_23,c_22,c_21])).

cnf(c_906,plain,
    ( ~ m2_orders_2(X0,sK4,sK5)
    | r2_hidden(X0,k4_orders_2(sK4,sK5)) ),
    inference(equality_resolution_simp,[status(thm)],[c_611])).

cnf(c_956,plain,
    ( ~ m2_orders_2(X0,sK4,sK5)
    | r2_hidden(X0,k4_orders_2(sK4,sK5)) ),
    inference(prop_impl,[status(thm)],[c_906])).

cnf(c_1820,plain,
    ( ~ m2_orders_2(sK3(sK4,sK5),sK4,sK5)
    | r2_hidden(sK3(sK4,sK5),k4_orders_2(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_956])).

cnf(c_1821,plain,
    ( m2_orders_2(sK3(sK4,sK5),sK4,sK5) != iProver_top
    | r2_hidden(sK3(sK4,sK5),k4_orders_2(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1820])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1868,plain,
    ( ~ r2_hidden(sK3(sK4,sK5),k4_orders_2(sK4,sK5))
    | ~ v1_xboole_0(k4_orders_2(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1877,plain,
    ( r2_hidden(sK3(sK4,sK5),k4_orders_2(sK4,sK5)) != iProver_top
    | v1_xboole_0(k4_orders_2(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1868])).

cnf(c_3014,plain,
    ( r1_tarski(sK0(k4_orders_2(sK4,sK5)),o_0_0_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2746,c_911,c_1821,c_1877])).

cnf(c_7,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1703,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2215,plain,
    ( r1_tarski(o_0_0_xboole_0,X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2212,c_1703])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1705,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3141,plain,
    ( o_0_0_xboole_0 = X0
    | r1_tarski(X0,o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2215,c_1705])).

cnf(c_3195,plain,
    ( sK0(k4_orders_2(sK4,sK5)) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_3014,c_3141])).

cnf(c_3354,plain,
    ( r2_hidden(o_0_0_xboole_0,k4_orders_2(sK4,sK5)) = iProver_top
    | v1_xboole_0(k4_orders_2(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3195,c_1709])).

cnf(c_3590,plain,
    ( r2_hidden(o_0_0_xboole_0,k4_orders_2(sK4,sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3354,c_911,c_1821,c_1877])).

cnf(c_3140,plain,
    ( k3_tarski(X0) = X1
    | r1_tarski(k3_tarski(X0),X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1702,c_1705])).

cnf(c_3669,plain,
    ( k3_tarski(k4_orders_2(sK4,sK5)) = X0
    | r1_tarski(o_0_0_xboole_0,X0) != iProver_top
    | r2_hidden(X0,k4_orders_2(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2217,c_3140])).

cnf(c_3674,plain,
    ( o_0_0_xboole_0 = X0
    | r1_tarski(o_0_0_xboole_0,X0) != iProver_top
    | r2_hidden(X0,k4_orders_2(sK4,sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3669,c_2217])).

cnf(c_15,plain,
    ( m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,k4_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_428,plain,
    ( m2_orders_2(X0,X1,X2)
    | ~ r2_hidden(X0,k4_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK4))
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_19])).

cnf(c_429,plain,
    ( m2_orders_2(X0,X1,sK5)
    | ~ r2_hidden(X0,k4_orders_2(X1,sK5))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_627,plain,
    ( m2_orders_2(X0,X1,sK5)
    | ~ r2_hidden(X0,k4_orders_2(X1,sK5))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK4))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_429,c_20])).

cnf(c_628,plain,
    ( m2_orders_2(X0,sK4,sK5)
    | ~ r2_hidden(X0,k4_orders_2(sK4,sK5))
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_627])).

cnf(c_632,plain,
    ( m2_orders_2(X0,sK4,sK5)
    | ~ r2_hidden(X0,k4_orders_2(sK4,sK5))
    | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_628,c_24,c_23,c_22,c_21])).

cnf(c_902,plain,
    ( m2_orders_2(X0,sK4,sK5)
    | ~ r2_hidden(X0,k4_orders_2(sK4,sK5)) ),
    inference(equality_resolution_simp,[status(thm)],[c_632])).

cnf(c_903,plain,
    ( m2_orders_2(X0,sK4,sK5) = iProver_top
    | r2_hidden(X0,k4_orders_2(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_902])).

cnf(c_11,plain,
    ( r1_xboole_0(k3_tarski(X0),X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1700,plain,
    ( r1_xboole_0(k3_tarski(X0),X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_9,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2216,plain,
    ( k3_tarski(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2212,c_9])).

cnf(c_2630,plain,
    ( r1_tarski(X0,o_0_0_xboole_0) = iProver_top
    | r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2216,c_1702])).

cnf(c_287,plain,
    ( ~ r2_hidden(X0,X1)
    | o_0_0_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_2])).

cnf(c_288,plain,
    ( ~ r2_hidden(X0,o_0_0_xboole_0) ),
    inference(unflattening,[status(thm)],[c_287])).

cnf(c_289,plain,
    ( r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_288])).

cnf(c_3299,plain,
    ( r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2630,c_289])).

cnf(c_3305,plain,
    ( r1_xboole_0(k3_tarski(o_0_0_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1700,c_3299])).

cnf(c_3312,plain,
    ( r1_xboole_0(o_0_0_xboole_0,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3305,c_2216])).

cnf(c_954,plain,
    ( m2_orders_2(X0,sK4,sK5)
    | ~ r2_hidden(X0,k4_orders_2(sK4,sK5)) ),
    inference(prop_impl,[status(thm)],[c_902])).

cnf(c_1698,plain,
    ( m2_orders_2(X0,sK4,sK5) = iProver_top
    | r2_hidden(X0,k4_orders_2(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_954])).

cnf(c_2524,plain,
    ( m2_orders_2(sK0(k4_orders_2(sK4,sK5)),sK4,sK5) = iProver_top
    | v1_xboole_0(k4_orders_2(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1709,c_1698])).

cnf(c_732,plain,
    ( m2_orders_2(X0,sK4,sK5)
    | v1_xboole_0(X1)
    | k4_orders_2(sK4,sK5) != X1
    | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4))
    | sK0(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_632])).

cnf(c_733,plain,
    ( m2_orders_2(sK0(k4_orders_2(sK4,sK5)),sK4,sK5)
    | v1_xboole_0(k4_orders_2(sK4,sK5)) ),
    inference(unflattening,[status(thm)],[c_732])).

cnf(c_734,plain,
    ( m2_orders_2(sK0(k4_orders_2(sK4,sK5)),sK4,sK5) = iProver_top
    | v1_xboole_0(k4_orders_2(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_733])).

cnf(c_3434,plain,
    ( m2_orders_2(sK0(k4_orders_2(sK4,sK5)),sK4,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2524,c_734,c_911,c_1821,c_1877])).

cnf(c_3438,plain,
    ( m2_orders_2(o_0_0_xboole_0,sK4,sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3434,c_3195])).

cnf(c_17,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(X3,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X3,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_395,plain,
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
    inference(resolution_lifted,[status(thm)],[c_17,c_19])).

cnf(c_396,plain,
    ( ~ m2_orders_2(X0,X1,sK5)
    | ~ m2_orders_2(X2,X1,sK5)
    | ~ r1_xboole_0(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_648,plain,
    ( ~ m2_orders_2(X0,X1,sK5)
    | ~ m2_orders_2(X2,X1,sK5)
    | ~ r1_xboole_0(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK4))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_396,c_20])).

cnf(c_649,plain,
    ( ~ m2_orders_2(X0,sK4,sK5)
    | ~ m2_orders_2(X1,sK4,sK5)
    | ~ r1_xboole_0(X0,X1)
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_648])).

cnf(c_653,plain,
    ( ~ m2_orders_2(X0,sK4,sK5)
    | ~ m2_orders_2(X1,sK4,sK5)
    | ~ r1_xboole_0(X0,X1)
    | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_649,c_24,c_23,c_22,c_21])).

cnf(c_898,plain,
    ( ~ m2_orders_2(X0,sK4,sK5)
    | ~ m2_orders_2(X1,sK4,sK5)
    | ~ r1_xboole_0(X0,X1) ),
    inference(equality_resolution_simp,[status(thm)],[c_653])).

cnf(c_1699,plain,
    ( m2_orders_2(X0,sK4,sK5) != iProver_top
    | m2_orders_2(X1,sK4,sK5) != iProver_top
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_898])).

cnf(c_3442,plain,
    ( m2_orders_2(X0,sK4,sK5) != iProver_top
    | r1_xboole_0(o_0_0_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3438,c_1699])).

cnf(c_3689,plain,
    ( r2_hidden(X0,k4_orders_2(sK4,sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3674,c_903,c_3312,c_3442])).

cnf(c_3700,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_3590,c_3689])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:33:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 1.30/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.30/1.01  
% 1.30/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.30/1.01  
% 1.30/1.01  ------  iProver source info
% 1.30/1.01  
% 1.30/1.01  git: date: 2020-06-30 10:37:57 +0100
% 1.30/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.30/1.01  git: non_committed_changes: false
% 1.30/1.01  git: last_make_outside_of_git: false
% 1.30/1.01  
% 1.30/1.01  ------ 
% 1.30/1.01  
% 1.30/1.01  ------ Input Options
% 1.30/1.01  
% 1.30/1.01  --out_options                           all
% 1.30/1.01  --tptp_safe_out                         true
% 1.30/1.01  --problem_path                          ""
% 1.30/1.01  --include_path                          ""
% 1.30/1.01  --clausifier                            res/vclausify_rel
% 1.30/1.01  --clausifier_options                    --mode clausify
% 1.30/1.01  --stdin                                 false
% 1.30/1.01  --stats_out                             all
% 1.30/1.01  
% 1.30/1.01  ------ General Options
% 1.30/1.01  
% 1.30/1.01  --fof                                   false
% 1.30/1.01  --time_out_real                         305.
% 1.30/1.01  --time_out_virtual                      -1.
% 1.30/1.01  --symbol_type_check                     false
% 1.30/1.01  --clausify_out                          false
% 1.30/1.01  --sig_cnt_out                           false
% 1.30/1.01  --trig_cnt_out                          false
% 1.30/1.01  --trig_cnt_out_tolerance                1.
% 1.30/1.01  --trig_cnt_out_sk_spl                   false
% 1.30/1.01  --abstr_cl_out                          false
% 1.30/1.01  
% 1.30/1.01  ------ Global Options
% 1.30/1.01  
% 1.30/1.01  --schedule                              default
% 1.30/1.01  --add_important_lit                     false
% 1.30/1.01  --prop_solver_per_cl                    1000
% 1.30/1.01  --min_unsat_core                        false
% 1.30/1.01  --soft_assumptions                      false
% 1.30/1.01  --soft_lemma_size                       3
% 1.30/1.01  --prop_impl_unit_size                   0
% 1.30/1.01  --prop_impl_unit                        []
% 1.30/1.01  --share_sel_clauses                     true
% 1.30/1.01  --reset_solvers                         false
% 1.30/1.01  --bc_imp_inh                            [conj_cone]
% 1.30/1.01  --conj_cone_tolerance                   3.
% 1.30/1.01  --extra_neg_conj                        none
% 1.30/1.01  --large_theory_mode                     true
% 1.30/1.01  --prolific_symb_bound                   200
% 1.30/1.01  --lt_threshold                          2000
% 1.30/1.01  --clause_weak_htbl                      true
% 1.30/1.01  --gc_record_bc_elim                     false
% 1.30/1.01  
% 1.30/1.01  ------ Preprocessing Options
% 1.30/1.01  
% 1.30/1.01  --preprocessing_flag                    true
% 1.30/1.01  --time_out_prep_mult                    0.1
% 1.30/1.01  --splitting_mode                        input
% 1.30/1.01  --splitting_grd                         true
% 1.30/1.01  --splitting_cvd                         false
% 1.30/1.01  --splitting_cvd_svl                     false
% 1.30/1.01  --splitting_nvd                         32
% 1.30/1.01  --sub_typing                            true
% 1.30/1.01  --prep_gs_sim                           true
% 1.30/1.01  --prep_unflatten                        true
% 1.30/1.01  --prep_res_sim                          true
% 1.30/1.01  --prep_upred                            true
% 1.30/1.01  --prep_sem_filter                       exhaustive
% 1.30/1.01  --prep_sem_filter_out                   false
% 1.30/1.01  --pred_elim                             true
% 1.30/1.01  --res_sim_input                         true
% 1.30/1.01  --eq_ax_congr_red                       true
% 1.30/1.01  --pure_diseq_elim                       true
% 1.30/1.01  --brand_transform                       false
% 1.30/1.01  --non_eq_to_eq                          false
% 1.30/1.01  --prep_def_merge                        true
% 1.30/1.01  --prep_def_merge_prop_impl              false
% 1.30/1.01  --prep_def_merge_mbd                    true
% 1.30/1.01  --prep_def_merge_tr_red                 false
% 1.30/1.01  --prep_def_merge_tr_cl                  false
% 1.30/1.01  --smt_preprocessing                     true
% 1.30/1.01  --smt_ac_axioms                         fast
% 1.30/1.01  --preprocessed_out                      false
% 1.30/1.01  --preprocessed_stats                    false
% 1.30/1.01  
% 1.30/1.01  ------ Abstraction refinement Options
% 1.30/1.01  
% 1.30/1.01  --abstr_ref                             []
% 1.30/1.01  --abstr_ref_prep                        false
% 1.30/1.01  --abstr_ref_until_sat                   false
% 1.30/1.01  --abstr_ref_sig_restrict                funpre
% 1.30/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.30/1.01  --abstr_ref_under                       []
% 1.30/1.01  
% 1.30/1.01  ------ SAT Options
% 1.30/1.01  
% 1.30/1.01  --sat_mode                              false
% 1.30/1.01  --sat_fm_restart_options                ""
% 1.30/1.01  --sat_gr_def                            false
% 1.30/1.01  --sat_epr_types                         true
% 1.30/1.01  --sat_non_cyclic_types                  false
% 1.30/1.01  --sat_finite_models                     false
% 1.30/1.01  --sat_fm_lemmas                         false
% 1.30/1.01  --sat_fm_prep                           false
% 1.30/1.01  --sat_fm_uc_incr                        true
% 1.30/1.01  --sat_out_model                         small
% 1.30/1.01  --sat_out_clauses                       false
% 1.30/1.01  
% 1.30/1.01  ------ QBF Options
% 1.30/1.01  
% 1.30/1.01  --qbf_mode                              false
% 1.30/1.01  --qbf_elim_univ                         false
% 1.30/1.01  --qbf_dom_inst                          none
% 1.30/1.01  --qbf_dom_pre_inst                      false
% 1.30/1.01  --qbf_sk_in                             false
% 1.30/1.01  --qbf_pred_elim                         true
% 1.30/1.01  --qbf_split                             512
% 1.30/1.01  
% 1.30/1.01  ------ BMC1 Options
% 1.30/1.01  
% 1.30/1.01  --bmc1_incremental                      false
% 1.30/1.01  --bmc1_axioms                           reachable_all
% 1.30/1.01  --bmc1_min_bound                        0
% 1.30/1.01  --bmc1_max_bound                        -1
% 1.30/1.01  --bmc1_max_bound_default                -1
% 1.30/1.01  --bmc1_symbol_reachability              true
% 1.30/1.01  --bmc1_property_lemmas                  false
% 1.30/1.01  --bmc1_k_induction                      false
% 1.30/1.01  --bmc1_non_equiv_states                 false
% 1.30/1.01  --bmc1_deadlock                         false
% 1.30/1.01  --bmc1_ucm                              false
% 1.30/1.01  --bmc1_add_unsat_core                   none
% 1.30/1.01  --bmc1_unsat_core_children              false
% 1.30/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.30/1.01  --bmc1_out_stat                         full
% 1.30/1.01  --bmc1_ground_init                      false
% 1.30/1.01  --bmc1_pre_inst_next_state              false
% 1.30/1.01  --bmc1_pre_inst_state                   false
% 1.30/1.01  --bmc1_pre_inst_reach_state             false
% 1.30/1.01  --bmc1_out_unsat_core                   false
% 1.30/1.01  --bmc1_aig_witness_out                  false
% 1.30/1.01  --bmc1_verbose                          false
% 1.30/1.01  --bmc1_dump_clauses_tptp                false
% 1.30/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.30/1.01  --bmc1_dump_file                        -
% 1.30/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.30/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.30/1.01  --bmc1_ucm_extend_mode                  1
% 1.30/1.01  --bmc1_ucm_init_mode                    2
% 1.30/1.01  --bmc1_ucm_cone_mode                    none
% 1.30/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.30/1.01  --bmc1_ucm_relax_model                  4
% 1.30/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.30/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.30/1.01  --bmc1_ucm_layered_model                none
% 1.30/1.01  --bmc1_ucm_max_lemma_size               10
% 1.30/1.01  
% 1.30/1.01  ------ AIG Options
% 1.30/1.01  
% 1.30/1.01  --aig_mode                              false
% 1.30/1.01  
% 1.30/1.01  ------ Instantiation Options
% 1.30/1.01  
% 1.30/1.01  --instantiation_flag                    true
% 1.30/1.01  --inst_sos_flag                         false
% 1.30/1.01  --inst_sos_phase                        true
% 1.30/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.30/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.30/1.01  --inst_lit_sel_side                     num_symb
% 1.30/1.01  --inst_solver_per_active                1400
% 1.30/1.01  --inst_solver_calls_frac                1.
% 1.30/1.01  --inst_passive_queue_type               priority_queues
% 1.30/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.30/1.01  --inst_passive_queues_freq              [25;2]
% 1.30/1.01  --inst_dismatching                      true
% 1.30/1.01  --inst_eager_unprocessed_to_passive     true
% 1.30/1.01  --inst_prop_sim_given                   true
% 1.30/1.01  --inst_prop_sim_new                     false
% 1.30/1.01  --inst_subs_new                         false
% 1.30/1.01  --inst_eq_res_simp                      false
% 1.30/1.01  --inst_subs_given                       false
% 1.30/1.01  --inst_orphan_elimination               true
% 1.30/1.01  --inst_learning_loop_flag               true
% 1.30/1.01  --inst_learning_start                   3000
% 1.30/1.01  --inst_learning_factor                  2
% 1.30/1.01  --inst_start_prop_sim_after_learn       3
% 1.30/1.01  --inst_sel_renew                        solver
% 1.30/1.01  --inst_lit_activity_flag                true
% 1.30/1.01  --inst_restr_to_given                   false
% 1.30/1.01  --inst_activity_threshold               500
% 1.30/1.01  --inst_out_proof                        true
% 1.30/1.01  
% 1.30/1.01  ------ Resolution Options
% 1.30/1.01  
% 1.30/1.01  --resolution_flag                       true
% 1.30/1.01  --res_lit_sel                           adaptive
% 1.30/1.01  --res_lit_sel_side                      none
% 1.30/1.01  --res_ordering                          kbo
% 1.30/1.01  --res_to_prop_solver                    active
% 1.30/1.01  --res_prop_simpl_new                    false
% 1.30/1.01  --res_prop_simpl_given                  true
% 1.30/1.01  --res_passive_queue_type                priority_queues
% 1.30/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.30/1.01  --res_passive_queues_freq               [15;5]
% 1.30/1.01  --res_forward_subs                      full
% 1.30/1.01  --res_backward_subs                     full
% 1.30/1.01  --res_forward_subs_resolution           true
% 1.30/1.01  --res_backward_subs_resolution          true
% 1.30/1.01  --res_orphan_elimination                true
% 1.30/1.01  --res_time_limit                        2.
% 1.30/1.01  --res_out_proof                         true
% 1.30/1.01  
% 1.30/1.01  ------ Superposition Options
% 1.30/1.01  
% 1.30/1.01  --superposition_flag                    true
% 1.30/1.01  --sup_passive_queue_type                priority_queues
% 1.30/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.30/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.30/1.01  --demod_completeness_check              fast
% 1.30/1.01  --demod_use_ground                      true
% 1.30/1.01  --sup_to_prop_solver                    passive
% 1.30/1.01  --sup_prop_simpl_new                    true
% 1.30/1.01  --sup_prop_simpl_given                  true
% 1.30/1.01  --sup_fun_splitting                     false
% 1.30/1.01  --sup_smt_interval                      50000
% 1.30/1.01  
% 1.30/1.01  ------ Superposition Simplification Setup
% 1.30/1.01  
% 1.30/1.01  --sup_indices_passive                   []
% 1.30/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.30/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.30/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.30/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.30/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.30/1.01  --sup_full_bw                           [BwDemod]
% 1.30/1.01  --sup_immed_triv                        [TrivRules]
% 1.30/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.30/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.30/1.01  --sup_immed_bw_main                     []
% 1.30/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.30/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.30/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.30/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.30/1.01  
% 1.30/1.01  ------ Combination Options
% 1.30/1.01  
% 1.30/1.01  --comb_res_mult                         3
% 1.30/1.01  --comb_sup_mult                         2
% 1.30/1.01  --comb_inst_mult                        10
% 1.30/1.01  
% 1.30/1.01  ------ Debug Options
% 1.30/1.01  
% 1.30/1.01  --dbg_backtrace                         false
% 1.30/1.01  --dbg_dump_prop_clauses                 false
% 1.30/1.01  --dbg_dump_prop_clauses_file            -
% 1.30/1.01  --dbg_out_stat                          false
% 1.30/1.01  ------ Parsing...
% 1.30/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.30/1.01  
% 1.30/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 1.30/1.01  
% 1.30/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.30/1.01  
% 1.30/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.30/1.01  ------ Proving...
% 1.30/1.01  ------ Problem Properties 
% 1.30/1.01  
% 1.30/1.01  
% 1.30/1.01  clauses                                 18
% 1.30/1.01  conjectures                             1
% 1.30/1.01  EPR                                     7
% 1.30/1.01  Horn                                    15
% 1.30/1.01  unary                                   6
% 1.30/1.01  binary                                  8
% 1.30/1.01  lits                                    34
% 1.30/1.01  lits eq                                 6
% 1.30/1.01  fd_pure                                 0
% 1.30/1.01  fd_pseudo                               0
% 1.30/1.01  fd_cond                                 3
% 1.30/1.01  fd_pseudo_cond                          1
% 1.30/1.01  AC symbols                              0
% 1.30/1.01  
% 1.30/1.01  ------ Schedule dynamic 5 is on 
% 1.30/1.01  
% 1.30/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.30/1.01  
% 1.30/1.01  
% 1.30/1.01  ------ 
% 1.30/1.01  Current options:
% 1.30/1.01  ------ 
% 1.30/1.01  
% 1.30/1.01  ------ Input Options
% 1.30/1.01  
% 1.30/1.01  --out_options                           all
% 1.30/1.01  --tptp_safe_out                         true
% 1.30/1.01  --problem_path                          ""
% 1.30/1.01  --include_path                          ""
% 1.30/1.01  --clausifier                            res/vclausify_rel
% 1.30/1.01  --clausifier_options                    --mode clausify
% 1.30/1.01  --stdin                                 false
% 1.30/1.01  --stats_out                             all
% 1.30/1.01  
% 1.30/1.01  ------ General Options
% 1.30/1.01  
% 1.30/1.01  --fof                                   false
% 1.30/1.01  --time_out_real                         305.
% 1.30/1.01  --time_out_virtual                      -1.
% 1.30/1.01  --symbol_type_check                     false
% 1.30/1.01  --clausify_out                          false
% 1.30/1.01  --sig_cnt_out                           false
% 1.30/1.01  --trig_cnt_out                          false
% 1.30/1.01  --trig_cnt_out_tolerance                1.
% 1.30/1.01  --trig_cnt_out_sk_spl                   false
% 1.30/1.01  --abstr_cl_out                          false
% 1.30/1.01  
% 1.30/1.01  ------ Global Options
% 1.30/1.01  
% 1.30/1.01  --schedule                              default
% 1.30/1.01  --add_important_lit                     false
% 1.30/1.01  --prop_solver_per_cl                    1000
% 1.30/1.01  --min_unsat_core                        false
% 1.30/1.01  --soft_assumptions                      false
% 1.30/1.01  --soft_lemma_size                       3
% 1.30/1.01  --prop_impl_unit_size                   0
% 1.30/1.01  --prop_impl_unit                        []
% 1.30/1.01  --share_sel_clauses                     true
% 1.30/1.01  --reset_solvers                         false
% 1.30/1.01  --bc_imp_inh                            [conj_cone]
% 1.30/1.01  --conj_cone_tolerance                   3.
% 1.30/1.01  --extra_neg_conj                        none
% 1.30/1.01  --large_theory_mode                     true
% 1.30/1.01  --prolific_symb_bound                   200
% 1.30/1.01  --lt_threshold                          2000
% 1.30/1.01  --clause_weak_htbl                      true
% 1.30/1.01  --gc_record_bc_elim                     false
% 1.30/1.01  
% 1.30/1.01  ------ Preprocessing Options
% 1.30/1.01  
% 1.30/1.01  --preprocessing_flag                    true
% 1.30/1.01  --time_out_prep_mult                    0.1
% 1.30/1.01  --splitting_mode                        input
% 1.30/1.01  --splitting_grd                         true
% 1.30/1.01  --splitting_cvd                         false
% 1.30/1.01  --splitting_cvd_svl                     false
% 1.30/1.01  --splitting_nvd                         32
% 1.30/1.01  --sub_typing                            true
% 1.30/1.01  --prep_gs_sim                           true
% 1.30/1.01  --prep_unflatten                        true
% 1.30/1.01  --prep_res_sim                          true
% 1.30/1.01  --prep_upred                            true
% 1.30/1.01  --prep_sem_filter                       exhaustive
% 1.30/1.01  --prep_sem_filter_out                   false
% 1.30/1.01  --pred_elim                             true
% 1.30/1.01  --res_sim_input                         true
% 1.30/1.01  --eq_ax_congr_red                       true
% 1.30/1.01  --pure_diseq_elim                       true
% 1.30/1.01  --brand_transform                       false
% 1.30/1.01  --non_eq_to_eq                          false
% 1.30/1.01  --prep_def_merge                        true
% 1.30/1.01  --prep_def_merge_prop_impl              false
% 1.30/1.01  --prep_def_merge_mbd                    true
% 1.30/1.01  --prep_def_merge_tr_red                 false
% 1.30/1.01  --prep_def_merge_tr_cl                  false
% 1.30/1.01  --smt_preprocessing                     true
% 1.30/1.01  --smt_ac_axioms                         fast
% 1.30/1.01  --preprocessed_out                      false
% 1.30/1.01  --preprocessed_stats                    false
% 1.30/1.01  
% 1.30/1.01  ------ Abstraction refinement Options
% 1.30/1.01  
% 1.30/1.01  --abstr_ref                             []
% 1.30/1.01  --abstr_ref_prep                        false
% 1.30/1.01  --abstr_ref_until_sat                   false
% 1.30/1.01  --abstr_ref_sig_restrict                funpre
% 1.30/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.30/1.01  --abstr_ref_under                       []
% 1.30/1.01  
% 1.30/1.01  ------ SAT Options
% 1.30/1.01  
% 1.30/1.01  --sat_mode                              false
% 1.30/1.01  --sat_fm_restart_options                ""
% 1.30/1.01  --sat_gr_def                            false
% 1.30/1.01  --sat_epr_types                         true
% 1.30/1.01  --sat_non_cyclic_types                  false
% 1.30/1.01  --sat_finite_models                     false
% 1.30/1.01  --sat_fm_lemmas                         false
% 1.30/1.01  --sat_fm_prep                           false
% 1.30/1.01  --sat_fm_uc_incr                        true
% 1.30/1.01  --sat_out_model                         small
% 1.30/1.01  --sat_out_clauses                       false
% 1.30/1.01  
% 1.30/1.01  ------ QBF Options
% 1.30/1.01  
% 1.30/1.01  --qbf_mode                              false
% 1.30/1.01  --qbf_elim_univ                         false
% 1.30/1.01  --qbf_dom_inst                          none
% 1.30/1.01  --qbf_dom_pre_inst                      false
% 1.30/1.01  --qbf_sk_in                             false
% 1.30/1.01  --qbf_pred_elim                         true
% 1.30/1.01  --qbf_split                             512
% 1.30/1.01  
% 1.30/1.01  ------ BMC1 Options
% 1.30/1.01  
% 1.30/1.01  --bmc1_incremental                      false
% 1.30/1.01  --bmc1_axioms                           reachable_all
% 1.30/1.01  --bmc1_min_bound                        0
% 1.30/1.01  --bmc1_max_bound                        -1
% 1.30/1.01  --bmc1_max_bound_default                -1
% 1.30/1.01  --bmc1_symbol_reachability              true
% 1.30/1.01  --bmc1_property_lemmas                  false
% 1.30/1.01  --bmc1_k_induction                      false
% 1.30/1.01  --bmc1_non_equiv_states                 false
% 1.30/1.01  --bmc1_deadlock                         false
% 1.30/1.01  --bmc1_ucm                              false
% 1.30/1.01  --bmc1_add_unsat_core                   none
% 1.30/1.01  --bmc1_unsat_core_children              false
% 1.30/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.30/1.01  --bmc1_out_stat                         full
% 1.30/1.01  --bmc1_ground_init                      false
% 1.30/1.01  --bmc1_pre_inst_next_state              false
% 1.30/1.01  --bmc1_pre_inst_state                   false
% 1.30/1.01  --bmc1_pre_inst_reach_state             false
% 1.30/1.01  --bmc1_out_unsat_core                   false
% 1.30/1.01  --bmc1_aig_witness_out                  false
% 1.30/1.01  --bmc1_verbose                          false
% 1.30/1.01  --bmc1_dump_clauses_tptp                false
% 1.30/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.30/1.01  --bmc1_dump_file                        -
% 1.30/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.30/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.30/1.01  --bmc1_ucm_extend_mode                  1
% 1.30/1.01  --bmc1_ucm_init_mode                    2
% 1.30/1.01  --bmc1_ucm_cone_mode                    none
% 1.30/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.30/1.01  --bmc1_ucm_relax_model                  4
% 1.30/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.30/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.30/1.01  --bmc1_ucm_layered_model                none
% 1.30/1.01  --bmc1_ucm_max_lemma_size               10
% 1.30/1.01  
% 1.30/1.01  ------ AIG Options
% 1.30/1.01  
% 1.30/1.01  --aig_mode                              false
% 1.30/1.01  
% 1.30/1.01  ------ Instantiation Options
% 1.30/1.01  
% 1.30/1.01  --instantiation_flag                    true
% 1.30/1.01  --inst_sos_flag                         false
% 1.30/1.01  --inst_sos_phase                        true
% 1.30/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.30/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.30/1.01  --inst_lit_sel_side                     none
% 1.30/1.01  --inst_solver_per_active                1400
% 1.30/1.01  --inst_solver_calls_frac                1.
% 1.30/1.01  --inst_passive_queue_type               priority_queues
% 1.30/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.30/1.01  --inst_passive_queues_freq              [25;2]
% 1.30/1.01  --inst_dismatching                      true
% 1.30/1.01  --inst_eager_unprocessed_to_passive     true
% 1.30/1.01  --inst_prop_sim_given                   true
% 1.30/1.01  --inst_prop_sim_new                     false
% 1.30/1.01  --inst_subs_new                         false
% 1.30/1.01  --inst_eq_res_simp                      false
% 1.30/1.01  --inst_subs_given                       false
% 1.30/1.01  --inst_orphan_elimination               true
% 1.30/1.01  --inst_learning_loop_flag               true
% 1.30/1.01  --inst_learning_start                   3000
% 1.30/1.01  --inst_learning_factor                  2
% 1.30/1.01  --inst_start_prop_sim_after_learn       3
% 1.30/1.01  --inst_sel_renew                        solver
% 1.30/1.01  --inst_lit_activity_flag                true
% 1.30/1.01  --inst_restr_to_given                   false
% 1.30/1.01  --inst_activity_threshold               500
% 1.30/1.01  --inst_out_proof                        true
% 1.30/1.01  
% 1.30/1.01  ------ Resolution Options
% 1.30/1.01  
% 1.30/1.01  --resolution_flag                       false
% 1.30/1.01  --res_lit_sel                           adaptive
% 1.30/1.01  --res_lit_sel_side                      none
% 1.30/1.01  --res_ordering                          kbo
% 1.30/1.01  --res_to_prop_solver                    active
% 1.30/1.01  --res_prop_simpl_new                    false
% 1.30/1.01  --res_prop_simpl_given                  true
% 1.30/1.01  --res_passive_queue_type                priority_queues
% 1.30/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.30/1.01  --res_passive_queues_freq               [15;5]
% 1.30/1.01  --res_forward_subs                      full
% 1.30/1.01  --res_backward_subs                     full
% 1.30/1.01  --res_forward_subs_resolution           true
% 1.30/1.01  --res_backward_subs_resolution          true
% 1.30/1.01  --res_orphan_elimination                true
% 1.30/1.01  --res_time_limit                        2.
% 1.30/1.01  --res_out_proof                         true
% 1.30/1.01  
% 1.30/1.01  ------ Superposition Options
% 1.30/1.01  
% 1.30/1.01  --superposition_flag                    true
% 1.30/1.01  --sup_passive_queue_type                priority_queues
% 1.30/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.30/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.30/1.01  --demod_completeness_check              fast
% 1.30/1.01  --demod_use_ground                      true
% 1.30/1.01  --sup_to_prop_solver                    passive
% 1.30/1.01  --sup_prop_simpl_new                    true
% 1.30/1.01  --sup_prop_simpl_given                  true
% 1.30/1.01  --sup_fun_splitting                     false
% 1.30/1.01  --sup_smt_interval                      50000
% 1.30/1.01  
% 1.30/1.01  ------ Superposition Simplification Setup
% 1.30/1.01  
% 1.30/1.01  --sup_indices_passive                   []
% 1.30/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.30/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.30/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.30/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.30/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.30/1.01  --sup_full_bw                           [BwDemod]
% 1.30/1.01  --sup_immed_triv                        [TrivRules]
% 1.30/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.30/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.30/1.01  --sup_immed_bw_main                     []
% 1.30/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.30/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.30/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.30/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.30/1.01  
% 1.30/1.01  ------ Combination Options
% 1.30/1.01  
% 1.30/1.01  --comb_res_mult                         3
% 1.30/1.01  --comb_sup_mult                         2
% 1.30/1.01  --comb_inst_mult                        10
% 1.30/1.01  
% 1.30/1.01  ------ Debug Options
% 1.30/1.01  
% 1.30/1.01  --dbg_backtrace                         false
% 1.30/1.01  --dbg_dump_prop_clauses                 false
% 1.30/1.01  --dbg_dump_prop_clauses_file            -
% 1.30/1.01  --dbg_out_stat                          false
% 1.30/1.01  
% 1.30/1.01  
% 1.30/1.01  
% 1.30/1.01  
% 1.30/1.01  ------ Proving...
% 1.30/1.01  
% 1.30/1.01  
% 1.30/1.01  % SZS status Theorem for theBenchmark.p
% 1.30/1.01  
% 1.30/1.01   Resolution empty clause
% 1.30/1.01  
% 1.30/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 1.30/1.01  
% 1.30/1.01  fof(f1,axiom,(
% 1.30/1.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.30/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.30/1.01  
% 1.30/1.01  fof(f25,plain,(
% 1.30/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.30/1.01    inference(nnf_transformation,[],[f1])).
% 1.30/1.01  
% 1.30/1.01  fof(f26,plain,(
% 1.30/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.30/1.01    inference(rectify,[],[f25])).
% 1.30/1.01  
% 1.30/1.01  fof(f27,plain,(
% 1.30/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.30/1.01    introduced(choice_axiom,[])).
% 1.30/1.01  
% 1.30/1.01  fof(f28,plain,(
% 1.30/1.01    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.30/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 1.30/1.01  
% 1.30/1.01  fof(f43,plain,(
% 1.30/1.01    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 1.30/1.01    inference(cnf_transformation,[],[f28])).
% 1.30/1.01  
% 1.30/1.01  fof(f2,axiom,(
% 1.30/1.01    v1_xboole_0(o_0_0_xboole_0)),
% 1.30/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.30/1.01  
% 1.30/1.01  fof(f44,plain,(
% 1.30/1.01    v1_xboole_0(o_0_0_xboole_0)),
% 1.30/1.01    inference(cnf_transformation,[],[f2])).
% 1.30/1.01  
% 1.30/1.01  fof(f3,axiom,(
% 1.30/1.01    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.30/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.30/1.01  
% 1.30/1.01  fof(f14,plain,(
% 1.30/1.01    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.30/1.01    inference(ennf_transformation,[],[f3])).
% 1.30/1.01  
% 1.30/1.01  fof(f45,plain,(
% 1.30/1.01    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.30/1.01    inference(cnf_transformation,[],[f14])).
% 1.30/1.01  
% 1.30/1.01  fof(f12,conjecture,(
% 1.30/1.01    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 1.30/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.30/1.01  
% 1.30/1.01  fof(f13,negated_conjecture,(
% 1.30/1.01    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 1.30/1.01    inference(negated_conjecture,[],[f12])).
% 1.30/1.01  
% 1.30/1.01  fof(f23,plain,(
% 1.30/1.01    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.30/1.01    inference(ennf_transformation,[],[f13])).
% 1.30/1.01  
% 1.30/1.01  fof(f24,plain,(
% 1.30/1.01    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.30/1.01    inference(flattening,[],[f23])).
% 1.30/1.01  
% 1.30/1.01  fof(f40,plain,(
% 1.30/1.01    ( ! [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) => (k1_xboole_0 = k3_tarski(k4_orders_2(X0,sK5)) & m1_orders_1(sK5,k1_orders_1(u1_struct_0(X0))))) )),
% 1.30/1.01    introduced(choice_axiom,[])).
% 1.30/1.01  
% 1.30/1.01  fof(f39,plain,(
% 1.30/1.01    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(sK4,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK4)))) & l1_orders_2(sK4) & v5_orders_2(sK4) & v4_orders_2(sK4) & v3_orders_2(sK4) & ~v2_struct_0(sK4))),
% 1.30/1.01    introduced(choice_axiom,[])).
% 1.30/1.01  
% 1.30/1.01  fof(f41,plain,(
% 1.30/1.01    (k1_xboole_0 = k3_tarski(k4_orders_2(sK4,sK5)) & m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4)))) & l1_orders_2(sK4) & v5_orders_2(sK4) & v4_orders_2(sK4) & v3_orders_2(sK4) & ~v2_struct_0(sK4)),
% 1.30/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f24,f40,f39])).
% 1.30/1.01  
% 1.30/1.01  fof(f66,plain,(
% 1.30/1.01    k1_xboole_0 = k3_tarski(k4_orders_2(sK4,sK5))),
% 1.30/1.01    inference(cnf_transformation,[],[f41])).
% 1.30/1.01  
% 1.30/1.01  fof(f6,axiom,(
% 1.30/1.01    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 1.30/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.30/1.01  
% 1.30/1.01  fof(f15,plain,(
% 1.30/1.01    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 1.30/1.01    inference(ennf_transformation,[],[f6])).
% 1.30/1.01  
% 1.30/1.01  fof(f50,plain,(
% 1.30/1.01    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 1.30/1.01    inference(cnf_transformation,[],[f15])).
% 1.30/1.01  
% 1.30/1.01  fof(f10,axiom,(
% 1.30/1.01    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ? [X2] : m2_orders_2(X2,X0,X1))),
% 1.30/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.30/1.01  
% 1.30/1.01  fof(f19,plain,(
% 1.30/1.01    ! [X0,X1] : (? [X2] : m2_orders_2(X2,X0,X1) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.30/1.01    inference(ennf_transformation,[],[f10])).
% 1.30/1.01  
% 1.30/1.01  fof(f20,plain,(
% 1.30/1.01    ! [X0,X1] : (? [X2] : m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.30/1.01    inference(flattening,[],[f19])).
% 1.30/1.01  
% 1.30/1.01  fof(f37,plain,(
% 1.30/1.01    ! [X1,X0] : (? [X2] : m2_orders_2(X2,X0,X1) => m2_orders_2(sK3(X0,X1),X0,X1))),
% 1.30/1.01    introduced(choice_axiom,[])).
% 1.30/1.01  
% 1.30/1.01  fof(f38,plain,(
% 1.30/1.01    ! [X0,X1] : (m2_orders_2(sK3(X0,X1),X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.30/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f37])).
% 1.30/1.01  
% 1.30/1.01  fof(f58,plain,(
% 1.30/1.01    ( ! [X0,X1] : (m2_orders_2(sK3(X0,X1),X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.30/1.01    inference(cnf_transformation,[],[f38])).
% 1.30/1.01  
% 1.30/1.01  fof(f65,plain,(
% 1.30/1.01    m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4)))),
% 1.30/1.01    inference(cnf_transformation,[],[f41])).
% 1.30/1.01  
% 1.30/1.01  fof(f64,plain,(
% 1.30/1.01    l1_orders_2(sK4)),
% 1.30/1.01    inference(cnf_transformation,[],[f41])).
% 1.30/1.01  
% 1.30/1.01  fof(f60,plain,(
% 1.30/1.01    ~v2_struct_0(sK4)),
% 1.30/1.01    inference(cnf_transformation,[],[f41])).
% 1.30/1.01  
% 1.30/1.01  fof(f61,plain,(
% 1.30/1.01    v3_orders_2(sK4)),
% 1.30/1.01    inference(cnf_transformation,[],[f41])).
% 1.30/1.01  
% 1.30/1.01  fof(f62,plain,(
% 1.30/1.01    v4_orders_2(sK4)),
% 1.30/1.01    inference(cnf_transformation,[],[f41])).
% 1.30/1.01  
% 1.30/1.01  fof(f63,plain,(
% 1.30/1.01    v5_orders_2(sK4)),
% 1.30/1.01    inference(cnf_transformation,[],[f41])).
% 1.30/1.01  
% 1.30/1.01  fof(f9,axiom,(
% 1.30/1.01    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1)))))),
% 1.30/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.30/1.01  
% 1.30/1.01  fof(f17,plain,(
% 1.30/1.01    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.30/1.01    inference(ennf_transformation,[],[f9])).
% 1.30/1.01  
% 1.30/1.01  fof(f18,plain,(
% 1.30/1.01    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.30/1.01    inference(flattening,[],[f17])).
% 1.30/1.01  
% 1.30/1.01  fof(f33,plain,(
% 1.30/1.01    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~m2_orders_2(X3,X0,X1)) & (m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.30/1.01    inference(nnf_transformation,[],[f18])).
% 1.30/1.01  
% 1.30/1.01  fof(f34,plain,(
% 1.30/1.01    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.30/1.01    inference(rectify,[],[f33])).
% 1.30/1.01  
% 1.30/1.01  fof(f35,plain,(
% 1.30/1.01    ! [X2,X1,X0] : (? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2))) => ((~m2_orders_2(sK2(X0,X1,X2),X0,X1) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (m2_orders_2(sK2(X0,X1,X2),X0,X1) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.30/1.01    introduced(choice_axiom,[])).
% 1.30/1.01  
% 1.30/1.01  fof(f36,plain,(
% 1.30/1.01    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ((~m2_orders_2(sK2(X0,X1,X2),X0,X1) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (m2_orders_2(sK2(X0,X1,X2),X0,X1) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.30/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).
% 1.30/1.01  
% 1.30/1.01  fof(f55,plain,(
% 1.30/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1) | k4_orders_2(X0,X1) != X2 | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.30/1.01    inference(cnf_transformation,[],[f36])).
% 1.30/1.01  
% 1.30/1.01  fof(f69,plain,(
% 1.30/1.01    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_orders_2(X0,X1)) | ~m2_orders_2(X4,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.30/1.01    inference(equality_resolution,[],[f55])).
% 1.30/1.01  
% 1.30/1.01  fof(f42,plain,(
% 1.30/1.01    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.30/1.01    inference(cnf_transformation,[],[f28])).
% 1.30/1.01  
% 1.30/1.01  fof(f5,axiom,(
% 1.30/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.30/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.30/1.01  
% 1.30/1.01  fof(f49,plain,(
% 1.30/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.30/1.01    inference(cnf_transformation,[],[f5])).
% 1.30/1.01  
% 1.30/1.01  fof(f4,axiom,(
% 1.30/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.30/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.30/1.01  
% 1.30/1.01  fof(f29,plain,(
% 1.30/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.30/1.01    inference(nnf_transformation,[],[f4])).
% 1.30/1.01  
% 1.30/1.01  fof(f30,plain,(
% 1.30/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.30/1.01    inference(flattening,[],[f29])).
% 1.30/1.01  
% 1.30/1.01  fof(f48,plain,(
% 1.30/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.30/1.01    inference(cnf_transformation,[],[f30])).
% 1.30/1.01  
% 1.30/1.01  fof(f54,plain,(
% 1.30/1.01    ( ! [X4,X2,X0,X1] : (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2) | k4_orders_2(X0,X1) != X2 | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.30/1.01    inference(cnf_transformation,[],[f36])).
% 1.30/1.01  
% 1.30/1.01  fof(f70,plain,(
% 1.30/1.01    ( ! [X4,X0,X1] : (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.30/1.01    inference(equality_resolution,[],[f54])).
% 1.30/1.01  
% 1.30/1.01  fof(f8,axiom,(
% 1.30/1.01    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_xboole_0(X2,X1)) => r1_xboole_0(k3_tarski(X0),X1))),
% 1.30/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.30/1.01  
% 1.30/1.01  fof(f16,plain,(
% 1.30/1.01    ! [X0,X1] : (r1_xboole_0(k3_tarski(X0),X1) | ? [X2] : (~r1_xboole_0(X2,X1) & r2_hidden(X2,X0)))),
% 1.30/1.01    inference(ennf_transformation,[],[f8])).
% 1.30/1.01  
% 1.30/1.01  fof(f31,plain,(
% 1.30/1.01    ! [X1,X0] : (? [X2] : (~r1_xboole_0(X2,X1) & r2_hidden(X2,X0)) => (~r1_xboole_0(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 1.30/1.01    introduced(choice_axiom,[])).
% 1.30/1.01  
% 1.30/1.01  fof(f32,plain,(
% 1.30/1.01    ! [X0,X1] : (r1_xboole_0(k3_tarski(X0),X1) | (~r1_xboole_0(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 1.30/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f31])).
% 1.30/1.01  
% 1.30/1.01  fof(f52,plain,(
% 1.30/1.01    ( ! [X0,X1] : (r1_xboole_0(k3_tarski(X0),X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 1.30/1.01    inference(cnf_transformation,[],[f32])).
% 1.30/1.01  
% 1.30/1.01  fof(f7,axiom,(
% 1.30/1.01    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.30/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.30/1.01  
% 1.30/1.01  fof(f51,plain,(
% 1.30/1.01    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.30/1.01    inference(cnf_transformation,[],[f7])).
% 1.30/1.01  
% 1.30/1.01  fof(f11,axiom,(
% 1.30/1.01    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => ~r1_xboole_0(X2,X3)))))),
% 1.30/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.30/1.01  
% 1.30/1.01  fof(f21,plain,(
% 1.30/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.30/1.01    inference(ennf_transformation,[],[f11])).
% 1.30/1.01  
% 1.30/1.01  fof(f22,plain,(
% 1.30/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.30/1.01    inference(flattening,[],[f21])).
% 1.30/1.01  
% 1.30/1.01  fof(f59,plain,(
% 1.30/1.01    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.30/1.01    inference(cnf_transformation,[],[f22])).
% 1.30/1.01  
% 1.30/1.01  cnf(c_0,plain,
% 1.30/1.01      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 1.30/1.01      inference(cnf_transformation,[],[f43]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_1709,plain,
% 1.30/1.01      ( r2_hidden(sK0(X0),X0) = iProver_top | v1_xboole_0(X0) = iProver_top ),
% 1.30/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_2,plain,
% 1.30/1.01      ( v1_xboole_0(o_0_0_xboole_0) ),
% 1.30/1.01      inference(cnf_transformation,[],[f44]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_1707,plain,
% 1.30/1.01      ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
% 1.30/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_3,plain,
% 1.30/1.01      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 1.30/1.01      inference(cnf_transformation,[],[f45]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_1706,plain,
% 1.30/1.01      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 1.30/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_2212,plain,
% 1.30/1.01      ( k1_xboole_0 = o_0_0_xboole_0 ),
% 1.30/1.01      inference(superposition,[status(thm)],[c_1707,c_1706]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_18,negated_conjecture,
% 1.30/1.01      ( k1_xboole_0 = k3_tarski(k4_orders_2(sK4,sK5)) ),
% 1.30/1.01      inference(cnf_transformation,[],[f66]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_2217,plain,
% 1.30/1.01      ( k3_tarski(k4_orders_2(sK4,sK5)) = o_0_0_xboole_0 ),
% 1.30/1.01      inference(demodulation,[status(thm)],[c_2212,c_18]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_8,plain,
% 1.30/1.01      ( r1_tarski(X0,k3_tarski(X1)) | ~ r2_hidden(X0,X1) ),
% 1.30/1.01      inference(cnf_transformation,[],[f50]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_1702,plain,
% 1.30/1.01      ( r1_tarski(X0,k3_tarski(X1)) = iProver_top
% 1.30/1.01      | r2_hidden(X0,X1) != iProver_top ),
% 1.30/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_2629,plain,
% 1.30/1.01      ( r1_tarski(X0,o_0_0_xboole_0) = iProver_top
% 1.30/1.01      | r2_hidden(X0,k4_orders_2(sK4,sK5)) != iProver_top ),
% 1.30/1.01      inference(superposition,[status(thm)],[c_2217,c_1702]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_2746,plain,
% 1.30/1.01      ( r1_tarski(sK0(k4_orders_2(sK4,sK5)),o_0_0_xboole_0) = iProver_top
% 1.30/1.01      | v1_xboole_0(k4_orders_2(sK4,sK5)) = iProver_top ),
% 1.30/1.01      inference(superposition,[status(thm)],[c_1709,c_2629]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_16,plain,
% 1.30/1.01      ( m2_orders_2(sK3(X0,X1),X0,X1)
% 1.30/1.01      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
% 1.30/1.01      | v2_struct_0(X0)
% 1.30/1.01      | ~ v3_orders_2(X0)
% 1.30/1.01      | ~ v4_orders_2(X0)
% 1.30/1.01      | ~ v5_orders_2(X0)
% 1.30/1.01      | ~ l1_orders_2(X0) ),
% 1.30/1.01      inference(cnf_transformation,[],[f58]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_19,negated_conjecture,
% 1.30/1.01      ( m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4))) ),
% 1.30/1.01      inference(cnf_transformation,[],[f65]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_302,plain,
% 1.30/1.01      ( m2_orders_2(sK3(X0,X1),X0,X1)
% 1.30/1.01      | v2_struct_0(X0)
% 1.30/1.01      | ~ v3_orders_2(X0)
% 1.30/1.01      | ~ v4_orders_2(X0)
% 1.30/1.01      | ~ v5_orders_2(X0)
% 1.30/1.01      | ~ l1_orders_2(X0)
% 1.30/1.01      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK4))
% 1.30/1.01      | sK5 != X1 ),
% 1.30/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_19]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_303,plain,
% 1.30/1.01      ( m2_orders_2(sK3(X0,sK5),X0,sK5)
% 1.30/1.01      | v2_struct_0(X0)
% 1.30/1.01      | ~ v3_orders_2(X0)
% 1.30/1.01      | ~ v4_orders_2(X0)
% 1.30/1.01      | ~ v5_orders_2(X0)
% 1.30/1.01      | ~ l1_orders_2(X0)
% 1.30/1.01      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK4)) ),
% 1.30/1.01      inference(unflattening,[status(thm)],[c_302]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_20,negated_conjecture,
% 1.30/1.01      ( l1_orders_2(sK4) ),
% 1.30/1.01      inference(cnf_transformation,[],[f64]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_592,plain,
% 1.30/1.01      ( m2_orders_2(sK3(X0,sK5),X0,sK5)
% 1.30/1.01      | v2_struct_0(X0)
% 1.30/1.01      | ~ v3_orders_2(X0)
% 1.30/1.01      | ~ v4_orders_2(X0)
% 1.30/1.01      | ~ v5_orders_2(X0)
% 1.30/1.01      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK4))
% 1.30/1.01      | sK4 != X0 ),
% 1.30/1.01      inference(resolution_lifted,[status(thm)],[c_303,c_20]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_593,plain,
% 1.30/1.01      ( m2_orders_2(sK3(sK4,sK5),sK4,sK5)
% 1.30/1.01      | v2_struct_0(sK4)
% 1.30/1.01      | ~ v3_orders_2(sK4)
% 1.30/1.01      | ~ v4_orders_2(sK4)
% 1.30/1.01      | ~ v5_orders_2(sK4)
% 1.30/1.01      | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4)) ),
% 1.30/1.01      inference(unflattening,[status(thm)],[c_592]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_24,negated_conjecture,
% 1.30/1.01      ( ~ v2_struct_0(sK4) ),
% 1.30/1.01      inference(cnf_transformation,[],[f60]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_23,negated_conjecture,
% 1.30/1.01      ( v3_orders_2(sK4) ),
% 1.30/1.01      inference(cnf_transformation,[],[f61]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_22,negated_conjecture,
% 1.30/1.01      ( v4_orders_2(sK4) ),
% 1.30/1.01      inference(cnf_transformation,[],[f62]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_21,negated_conjecture,
% 1.30/1.01      ( v5_orders_2(sK4) ),
% 1.30/1.01      inference(cnf_transformation,[],[f63]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_595,plain,
% 1.30/1.01      ( m2_orders_2(sK3(sK4,sK5),sK4,sK5)
% 1.30/1.01      | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4)) ),
% 1.30/1.01      inference(global_propositional_subsumption,
% 1.30/1.01                [status(thm)],
% 1.30/1.01                [c_593,c_24,c_23,c_22,c_21]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_910,plain,
% 1.30/1.01      ( m2_orders_2(sK3(sK4,sK5),sK4,sK5) ),
% 1.30/1.01      inference(equality_resolution_simp,[status(thm)],[c_595]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_911,plain,
% 1.30/1.01      ( m2_orders_2(sK3(sK4,sK5),sK4,sK5) = iProver_top ),
% 1.30/1.01      inference(predicate_to_equality,[status(thm)],[c_910]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_14,plain,
% 1.30/1.01      ( ~ m2_orders_2(X0,X1,X2)
% 1.30/1.01      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.30/1.01      | r2_hidden(X0,k4_orders_2(X1,X2))
% 1.30/1.01      | v2_struct_0(X1)
% 1.30/1.01      | ~ v3_orders_2(X1)
% 1.30/1.01      | ~ v4_orders_2(X1)
% 1.30/1.01      | ~ v5_orders_2(X1)
% 1.30/1.01      | ~ l1_orders_2(X1) ),
% 1.30/1.01      inference(cnf_transformation,[],[f69]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_458,plain,
% 1.30/1.01      ( ~ m2_orders_2(X0,X1,X2)
% 1.30/1.01      | r2_hidden(X0,k4_orders_2(X1,X2))
% 1.30/1.01      | v2_struct_0(X1)
% 1.30/1.01      | ~ v3_orders_2(X1)
% 1.30/1.01      | ~ v4_orders_2(X1)
% 1.30/1.01      | ~ v5_orders_2(X1)
% 1.30/1.01      | ~ l1_orders_2(X1)
% 1.30/1.01      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK4))
% 1.30/1.01      | sK5 != X2 ),
% 1.30/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_19]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_459,plain,
% 1.30/1.01      ( ~ m2_orders_2(X0,X1,sK5)
% 1.30/1.01      | r2_hidden(X0,k4_orders_2(X1,sK5))
% 1.30/1.01      | v2_struct_0(X1)
% 1.30/1.01      | ~ v3_orders_2(X1)
% 1.30/1.01      | ~ v4_orders_2(X1)
% 1.30/1.01      | ~ v5_orders_2(X1)
% 1.30/1.01      | ~ l1_orders_2(X1)
% 1.30/1.01      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK4)) ),
% 1.30/1.01      inference(unflattening,[status(thm)],[c_458]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_606,plain,
% 1.30/1.01      ( ~ m2_orders_2(X0,X1,sK5)
% 1.30/1.01      | r2_hidden(X0,k4_orders_2(X1,sK5))
% 1.30/1.01      | v2_struct_0(X1)
% 1.30/1.01      | ~ v3_orders_2(X1)
% 1.30/1.01      | ~ v4_orders_2(X1)
% 1.30/1.01      | ~ v5_orders_2(X1)
% 1.30/1.01      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK4))
% 1.30/1.01      | sK4 != X1 ),
% 1.30/1.01      inference(resolution_lifted,[status(thm)],[c_459,c_20]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_607,plain,
% 1.30/1.01      ( ~ m2_orders_2(X0,sK4,sK5)
% 1.30/1.01      | r2_hidden(X0,k4_orders_2(sK4,sK5))
% 1.30/1.01      | v2_struct_0(sK4)
% 1.30/1.01      | ~ v3_orders_2(sK4)
% 1.30/1.01      | ~ v4_orders_2(sK4)
% 1.30/1.01      | ~ v5_orders_2(sK4)
% 1.30/1.01      | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4)) ),
% 1.30/1.01      inference(unflattening,[status(thm)],[c_606]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_611,plain,
% 1.30/1.01      ( ~ m2_orders_2(X0,sK4,sK5)
% 1.30/1.01      | r2_hidden(X0,k4_orders_2(sK4,sK5))
% 1.30/1.01      | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4)) ),
% 1.30/1.01      inference(global_propositional_subsumption,
% 1.30/1.01                [status(thm)],
% 1.30/1.01                [c_607,c_24,c_23,c_22,c_21]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_906,plain,
% 1.30/1.01      ( ~ m2_orders_2(X0,sK4,sK5) | r2_hidden(X0,k4_orders_2(sK4,sK5)) ),
% 1.30/1.01      inference(equality_resolution_simp,[status(thm)],[c_611]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_956,plain,
% 1.30/1.01      ( ~ m2_orders_2(X0,sK4,sK5) | r2_hidden(X0,k4_orders_2(sK4,sK5)) ),
% 1.30/1.01      inference(prop_impl,[status(thm)],[c_906]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_1820,plain,
% 1.30/1.01      ( ~ m2_orders_2(sK3(sK4,sK5),sK4,sK5)
% 1.30/1.01      | r2_hidden(sK3(sK4,sK5),k4_orders_2(sK4,sK5)) ),
% 1.30/1.01      inference(instantiation,[status(thm)],[c_956]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_1821,plain,
% 1.30/1.01      ( m2_orders_2(sK3(sK4,sK5),sK4,sK5) != iProver_top
% 1.30/1.01      | r2_hidden(sK3(sK4,sK5),k4_orders_2(sK4,sK5)) = iProver_top ),
% 1.30/1.01      inference(predicate_to_equality,[status(thm)],[c_1820]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_1,plain,
% 1.30/1.01      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 1.30/1.01      inference(cnf_transformation,[],[f42]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_1868,plain,
% 1.30/1.01      ( ~ r2_hidden(sK3(sK4,sK5),k4_orders_2(sK4,sK5))
% 1.30/1.01      | ~ v1_xboole_0(k4_orders_2(sK4,sK5)) ),
% 1.30/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_1877,plain,
% 1.30/1.01      ( r2_hidden(sK3(sK4,sK5),k4_orders_2(sK4,sK5)) != iProver_top
% 1.30/1.01      | v1_xboole_0(k4_orders_2(sK4,sK5)) != iProver_top ),
% 1.30/1.01      inference(predicate_to_equality,[status(thm)],[c_1868]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_3014,plain,
% 1.30/1.01      ( r1_tarski(sK0(k4_orders_2(sK4,sK5)),o_0_0_xboole_0) = iProver_top ),
% 1.30/1.01      inference(global_propositional_subsumption,
% 1.30/1.01                [status(thm)],
% 1.30/1.01                [c_2746,c_911,c_1821,c_1877]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_7,plain,
% 1.30/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 1.30/1.01      inference(cnf_transformation,[],[f49]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_1703,plain,
% 1.30/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 1.30/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_2215,plain,
% 1.30/1.01      ( r1_tarski(o_0_0_xboole_0,X0) = iProver_top ),
% 1.30/1.01      inference(demodulation,[status(thm)],[c_2212,c_1703]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_4,plain,
% 1.30/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 1.30/1.01      inference(cnf_transformation,[],[f48]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_1705,plain,
% 1.30/1.01      ( X0 = X1
% 1.30/1.01      | r1_tarski(X0,X1) != iProver_top
% 1.30/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 1.30/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_3141,plain,
% 1.30/1.01      ( o_0_0_xboole_0 = X0 | r1_tarski(X0,o_0_0_xboole_0) != iProver_top ),
% 1.30/1.01      inference(superposition,[status(thm)],[c_2215,c_1705]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_3195,plain,
% 1.30/1.01      ( sK0(k4_orders_2(sK4,sK5)) = o_0_0_xboole_0 ),
% 1.30/1.01      inference(superposition,[status(thm)],[c_3014,c_3141]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_3354,plain,
% 1.30/1.01      ( r2_hidden(o_0_0_xboole_0,k4_orders_2(sK4,sK5)) = iProver_top
% 1.30/1.01      | v1_xboole_0(k4_orders_2(sK4,sK5)) = iProver_top ),
% 1.30/1.01      inference(superposition,[status(thm)],[c_3195,c_1709]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_3590,plain,
% 1.30/1.01      ( r2_hidden(o_0_0_xboole_0,k4_orders_2(sK4,sK5)) = iProver_top ),
% 1.30/1.01      inference(global_propositional_subsumption,
% 1.30/1.01                [status(thm)],
% 1.30/1.01                [c_3354,c_911,c_1821,c_1877]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_3140,plain,
% 1.30/1.01      ( k3_tarski(X0) = X1
% 1.30/1.01      | r1_tarski(k3_tarski(X0),X1) != iProver_top
% 1.30/1.01      | r2_hidden(X1,X0) != iProver_top ),
% 1.30/1.01      inference(superposition,[status(thm)],[c_1702,c_1705]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_3669,plain,
% 1.30/1.01      ( k3_tarski(k4_orders_2(sK4,sK5)) = X0
% 1.30/1.01      | r1_tarski(o_0_0_xboole_0,X0) != iProver_top
% 1.30/1.01      | r2_hidden(X0,k4_orders_2(sK4,sK5)) != iProver_top ),
% 1.30/1.01      inference(superposition,[status(thm)],[c_2217,c_3140]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_3674,plain,
% 1.30/1.01      ( o_0_0_xboole_0 = X0
% 1.30/1.01      | r1_tarski(o_0_0_xboole_0,X0) != iProver_top
% 1.30/1.01      | r2_hidden(X0,k4_orders_2(sK4,sK5)) != iProver_top ),
% 1.30/1.01      inference(demodulation,[status(thm)],[c_3669,c_2217]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_15,plain,
% 1.30/1.01      ( m2_orders_2(X0,X1,X2)
% 1.30/1.01      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.30/1.01      | ~ r2_hidden(X0,k4_orders_2(X1,X2))
% 1.30/1.01      | v2_struct_0(X1)
% 1.30/1.01      | ~ v3_orders_2(X1)
% 1.30/1.01      | ~ v4_orders_2(X1)
% 1.30/1.01      | ~ v5_orders_2(X1)
% 1.30/1.01      | ~ l1_orders_2(X1) ),
% 1.30/1.01      inference(cnf_transformation,[],[f70]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_428,plain,
% 1.30/1.01      ( m2_orders_2(X0,X1,X2)
% 1.30/1.01      | ~ r2_hidden(X0,k4_orders_2(X1,X2))
% 1.30/1.01      | v2_struct_0(X1)
% 1.30/1.01      | ~ v3_orders_2(X1)
% 1.30/1.01      | ~ v4_orders_2(X1)
% 1.30/1.01      | ~ v5_orders_2(X1)
% 1.30/1.01      | ~ l1_orders_2(X1)
% 1.30/1.01      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK4))
% 1.30/1.01      | sK5 != X2 ),
% 1.30/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_19]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_429,plain,
% 1.30/1.01      ( m2_orders_2(X0,X1,sK5)
% 1.30/1.01      | ~ r2_hidden(X0,k4_orders_2(X1,sK5))
% 1.30/1.01      | v2_struct_0(X1)
% 1.30/1.01      | ~ v3_orders_2(X1)
% 1.30/1.01      | ~ v4_orders_2(X1)
% 1.30/1.01      | ~ v5_orders_2(X1)
% 1.30/1.01      | ~ l1_orders_2(X1)
% 1.30/1.01      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK4)) ),
% 1.30/1.01      inference(unflattening,[status(thm)],[c_428]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_627,plain,
% 1.30/1.01      ( m2_orders_2(X0,X1,sK5)
% 1.30/1.01      | ~ r2_hidden(X0,k4_orders_2(X1,sK5))
% 1.30/1.01      | v2_struct_0(X1)
% 1.30/1.01      | ~ v3_orders_2(X1)
% 1.30/1.01      | ~ v4_orders_2(X1)
% 1.30/1.01      | ~ v5_orders_2(X1)
% 1.30/1.01      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK4))
% 1.30/1.01      | sK4 != X1 ),
% 1.30/1.01      inference(resolution_lifted,[status(thm)],[c_429,c_20]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_628,plain,
% 1.30/1.01      ( m2_orders_2(X0,sK4,sK5)
% 1.30/1.01      | ~ r2_hidden(X0,k4_orders_2(sK4,sK5))
% 1.30/1.01      | v2_struct_0(sK4)
% 1.30/1.01      | ~ v3_orders_2(sK4)
% 1.30/1.01      | ~ v4_orders_2(sK4)
% 1.30/1.01      | ~ v5_orders_2(sK4)
% 1.30/1.01      | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4)) ),
% 1.30/1.01      inference(unflattening,[status(thm)],[c_627]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_632,plain,
% 1.30/1.01      ( m2_orders_2(X0,sK4,sK5)
% 1.30/1.01      | ~ r2_hidden(X0,k4_orders_2(sK4,sK5))
% 1.30/1.01      | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4)) ),
% 1.30/1.01      inference(global_propositional_subsumption,
% 1.30/1.01                [status(thm)],
% 1.30/1.01                [c_628,c_24,c_23,c_22,c_21]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_902,plain,
% 1.30/1.01      ( m2_orders_2(X0,sK4,sK5) | ~ r2_hidden(X0,k4_orders_2(sK4,sK5)) ),
% 1.30/1.01      inference(equality_resolution_simp,[status(thm)],[c_632]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_903,plain,
% 1.30/1.01      ( m2_orders_2(X0,sK4,sK5) = iProver_top
% 1.30/1.01      | r2_hidden(X0,k4_orders_2(sK4,sK5)) != iProver_top ),
% 1.30/1.01      inference(predicate_to_equality,[status(thm)],[c_902]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_11,plain,
% 1.30/1.01      ( r1_xboole_0(k3_tarski(X0),X1) | r2_hidden(sK1(X0,X1),X0) ),
% 1.30/1.01      inference(cnf_transformation,[],[f52]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_1700,plain,
% 1.30/1.01      ( r1_xboole_0(k3_tarski(X0),X1) = iProver_top
% 1.30/1.01      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 1.30/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_9,plain,
% 1.30/1.01      ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
% 1.30/1.01      inference(cnf_transformation,[],[f51]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_2216,plain,
% 1.30/1.01      ( k3_tarski(o_0_0_xboole_0) = o_0_0_xboole_0 ),
% 1.30/1.01      inference(demodulation,[status(thm)],[c_2212,c_9]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_2630,plain,
% 1.30/1.01      ( r1_tarski(X0,o_0_0_xboole_0) = iProver_top
% 1.30/1.01      | r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
% 1.30/1.01      inference(superposition,[status(thm)],[c_2216,c_1702]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_287,plain,
% 1.30/1.01      ( ~ r2_hidden(X0,X1) | o_0_0_xboole_0 != X1 ),
% 1.30/1.01      inference(resolution_lifted,[status(thm)],[c_1,c_2]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_288,plain,
% 1.30/1.01      ( ~ r2_hidden(X0,o_0_0_xboole_0) ),
% 1.30/1.01      inference(unflattening,[status(thm)],[c_287]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_289,plain,
% 1.30/1.01      ( r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
% 1.30/1.01      inference(predicate_to_equality,[status(thm)],[c_288]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_3299,plain,
% 1.30/1.01      ( r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
% 1.30/1.01      inference(global_propositional_subsumption,[status(thm)],[c_2630,c_289]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_3305,plain,
% 1.30/1.01      ( r1_xboole_0(k3_tarski(o_0_0_xboole_0),X0) = iProver_top ),
% 1.30/1.01      inference(superposition,[status(thm)],[c_1700,c_3299]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_3312,plain,
% 1.30/1.01      ( r1_xboole_0(o_0_0_xboole_0,X0) = iProver_top ),
% 1.30/1.01      inference(light_normalisation,[status(thm)],[c_3305,c_2216]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_954,plain,
% 1.30/1.01      ( m2_orders_2(X0,sK4,sK5) | ~ r2_hidden(X0,k4_orders_2(sK4,sK5)) ),
% 1.30/1.01      inference(prop_impl,[status(thm)],[c_902]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_1698,plain,
% 1.30/1.01      ( m2_orders_2(X0,sK4,sK5) = iProver_top
% 1.30/1.01      | r2_hidden(X0,k4_orders_2(sK4,sK5)) != iProver_top ),
% 1.30/1.01      inference(predicate_to_equality,[status(thm)],[c_954]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_2524,plain,
% 1.30/1.01      ( m2_orders_2(sK0(k4_orders_2(sK4,sK5)),sK4,sK5) = iProver_top
% 1.30/1.01      | v1_xboole_0(k4_orders_2(sK4,sK5)) = iProver_top ),
% 1.30/1.01      inference(superposition,[status(thm)],[c_1709,c_1698]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_732,plain,
% 1.30/1.01      ( m2_orders_2(X0,sK4,sK5)
% 1.30/1.01      | v1_xboole_0(X1)
% 1.30/1.01      | k4_orders_2(sK4,sK5) != X1
% 1.30/1.01      | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4))
% 1.30/1.01      | sK0(X1) != X0 ),
% 1.30/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_632]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_733,plain,
% 1.30/1.01      ( m2_orders_2(sK0(k4_orders_2(sK4,sK5)),sK4,sK5)
% 1.30/1.01      | v1_xboole_0(k4_orders_2(sK4,sK5)) ),
% 1.30/1.01      inference(unflattening,[status(thm)],[c_732]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_734,plain,
% 1.30/1.01      ( m2_orders_2(sK0(k4_orders_2(sK4,sK5)),sK4,sK5) = iProver_top
% 1.30/1.01      | v1_xboole_0(k4_orders_2(sK4,sK5)) = iProver_top ),
% 1.30/1.01      inference(predicate_to_equality,[status(thm)],[c_733]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_3434,plain,
% 1.30/1.01      ( m2_orders_2(sK0(k4_orders_2(sK4,sK5)),sK4,sK5) = iProver_top ),
% 1.30/1.01      inference(global_propositional_subsumption,
% 1.30/1.01                [status(thm)],
% 1.30/1.01                [c_2524,c_734,c_911,c_1821,c_1877]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_3438,plain,
% 1.30/1.01      ( m2_orders_2(o_0_0_xboole_0,sK4,sK5) = iProver_top ),
% 1.30/1.01      inference(light_normalisation,[status(thm)],[c_3434,c_3195]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_17,plain,
% 1.30/1.01      ( ~ m2_orders_2(X0,X1,X2)
% 1.30/1.01      | ~ m2_orders_2(X3,X1,X2)
% 1.30/1.01      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.30/1.01      | ~ r1_xboole_0(X3,X0)
% 1.30/1.01      | v2_struct_0(X1)
% 1.30/1.01      | ~ v3_orders_2(X1)
% 1.30/1.01      | ~ v4_orders_2(X1)
% 1.30/1.01      | ~ v5_orders_2(X1)
% 1.30/1.01      | ~ l1_orders_2(X1) ),
% 1.30/1.01      inference(cnf_transformation,[],[f59]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_395,plain,
% 1.30/1.01      ( ~ m2_orders_2(X0,X1,X2)
% 1.30/1.01      | ~ m2_orders_2(X3,X1,X2)
% 1.30/1.01      | ~ r1_xboole_0(X3,X0)
% 1.30/1.01      | v2_struct_0(X1)
% 1.30/1.01      | ~ v3_orders_2(X1)
% 1.30/1.01      | ~ v4_orders_2(X1)
% 1.30/1.01      | ~ v5_orders_2(X1)
% 1.30/1.01      | ~ l1_orders_2(X1)
% 1.30/1.01      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK4))
% 1.30/1.01      | sK5 != X2 ),
% 1.30/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_19]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_396,plain,
% 1.30/1.01      ( ~ m2_orders_2(X0,X1,sK5)
% 1.30/1.01      | ~ m2_orders_2(X2,X1,sK5)
% 1.30/1.01      | ~ r1_xboole_0(X0,X2)
% 1.30/1.01      | v2_struct_0(X1)
% 1.30/1.01      | ~ v3_orders_2(X1)
% 1.30/1.01      | ~ v4_orders_2(X1)
% 1.30/1.01      | ~ v5_orders_2(X1)
% 1.30/1.01      | ~ l1_orders_2(X1)
% 1.30/1.01      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK4)) ),
% 1.30/1.01      inference(unflattening,[status(thm)],[c_395]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_648,plain,
% 1.30/1.01      ( ~ m2_orders_2(X0,X1,sK5)
% 1.30/1.01      | ~ m2_orders_2(X2,X1,sK5)
% 1.30/1.01      | ~ r1_xboole_0(X0,X2)
% 1.30/1.01      | v2_struct_0(X1)
% 1.30/1.01      | ~ v3_orders_2(X1)
% 1.30/1.01      | ~ v4_orders_2(X1)
% 1.30/1.01      | ~ v5_orders_2(X1)
% 1.30/1.01      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK4))
% 1.30/1.01      | sK4 != X1 ),
% 1.30/1.01      inference(resolution_lifted,[status(thm)],[c_396,c_20]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_649,plain,
% 1.30/1.01      ( ~ m2_orders_2(X0,sK4,sK5)
% 1.30/1.01      | ~ m2_orders_2(X1,sK4,sK5)
% 1.30/1.01      | ~ r1_xboole_0(X0,X1)
% 1.30/1.01      | v2_struct_0(sK4)
% 1.30/1.01      | ~ v3_orders_2(sK4)
% 1.30/1.01      | ~ v4_orders_2(sK4)
% 1.30/1.01      | ~ v5_orders_2(sK4)
% 1.30/1.01      | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4)) ),
% 1.30/1.01      inference(unflattening,[status(thm)],[c_648]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_653,plain,
% 1.30/1.01      ( ~ m2_orders_2(X0,sK4,sK5)
% 1.30/1.01      | ~ m2_orders_2(X1,sK4,sK5)
% 1.30/1.01      | ~ r1_xboole_0(X0,X1)
% 1.30/1.01      | k1_orders_1(u1_struct_0(sK4)) != k1_orders_1(u1_struct_0(sK4)) ),
% 1.30/1.01      inference(global_propositional_subsumption,
% 1.30/1.01                [status(thm)],
% 1.30/1.01                [c_649,c_24,c_23,c_22,c_21]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_898,plain,
% 1.30/1.01      ( ~ m2_orders_2(X0,sK4,sK5)
% 1.30/1.01      | ~ m2_orders_2(X1,sK4,sK5)
% 1.30/1.01      | ~ r1_xboole_0(X0,X1) ),
% 1.30/1.01      inference(equality_resolution_simp,[status(thm)],[c_653]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_1699,plain,
% 1.30/1.01      ( m2_orders_2(X0,sK4,sK5) != iProver_top
% 1.30/1.01      | m2_orders_2(X1,sK4,sK5) != iProver_top
% 1.30/1.01      | r1_xboole_0(X0,X1) != iProver_top ),
% 1.30/1.01      inference(predicate_to_equality,[status(thm)],[c_898]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_3442,plain,
% 1.30/1.01      ( m2_orders_2(X0,sK4,sK5) != iProver_top
% 1.30/1.01      | r1_xboole_0(o_0_0_xboole_0,X0) != iProver_top ),
% 1.30/1.01      inference(superposition,[status(thm)],[c_3438,c_1699]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_3689,plain,
% 1.30/1.01      ( r2_hidden(X0,k4_orders_2(sK4,sK5)) != iProver_top ),
% 1.30/1.01      inference(global_propositional_subsumption,
% 1.30/1.01                [status(thm)],
% 1.30/1.01                [c_3674,c_903,c_3312,c_3442]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_3700,plain,
% 1.30/1.01      ( $false ),
% 1.30/1.01      inference(superposition,[status(thm)],[c_3590,c_3689]) ).
% 1.30/1.01  
% 1.30/1.01  
% 1.30/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 1.30/1.01  
% 1.30/1.01  ------                               Statistics
% 1.30/1.01  
% 1.30/1.01  ------ General
% 1.30/1.01  
% 1.30/1.01  abstr_ref_over_cycles:                  0
% 1.30/1.01  abstr_ref_under_cycles:                 0
% 1.30/1.01  gc_basic_clause_elim:                   0
% 1.30/1.01  forced_gc_time:                         0
% 1.30/1.01  parsing_time:                           0.011
% 1.30/1.01  unif_index_cands_time:                  0.
% 1.30/1.01  unif_index_add_time:                    0.
% 1.30/1.01  orderings_time:                         0.
% 1.30/1.01  out_proof_time:                         0.01
% 1.30/1.01  total_time:                             0.13
% 1.30/1.01  num_of_symbols:                         54
% 1.30/1.01  num_of_terms:                           2522
% 1.30/1.01  
% 1.30/1.01  ------ Preprocessing
% 1.30/1.01  
% 1.30/1.01  num_of_splits:                          0
% 1.30/1.01  num_of_split_atoms:                     0
% 1.30/1.01  num_of_reused_defs:                     0
% 1.30/1.01  num_eq_ax_congr_red:                    21
% 1.30/1.01  num_of_sem_filtered_clauses:            1
% 1.30/1.01  num_of_subtypes:                        0
% 1.30/1.01  monotx_restored_types:                  0
% 1.30/1.01  sat_num_of_epr_types:                   0
% 1.30/1.01  sat_num_of_non_cyclic_types:            0
% 1.30/1.01  sat_guarded_non_collapsed_types:        0
% 1.30/1.01  num_pure_diseq_elim:                    0
% 1.30/1.01  simp_replaced_by:                       0
% 1.30/1.01  res_preprocessed:                       101
% 1.30/1.01  prep_upred:                             0
% 1.30/1.01  prep_unflattend:                        70
% 1.30/1.01  smt_new_axioms:                         0
% 1.30/1.01  pred_elim_cands:                        5
% 1.30/1.01  pred_elim:                              6
% 1.30/1.01  pred_elim_cl:                           6
% 1.30/1.01  pred_elim_cycles:                       10
% 1.30/1.01  merged_defs:                            6
% 1.30/1.01  merged_defs_ncl:                        0
% 1.30/1.01  bin_hyper_res:                          6
% 1.30/1.01  prep_cycles:                            4
% 1.30/1.01  pred_elim_time:                         0.015
% 1.30/1.01  splitting_time:                         0.
% 1.30/1.01  sem_filter_time:                        0.
% 1.30/1.01  monotx_time:                            0.001
% 1.30/1.01  subtype_inf_time:                       0.
% 1.30/1.01  
% 1.30/1.01  ------ Problem properties
% 1.30/1.01  
% 1.30/1.01  clauses:                                18
% 1.30/1.01  conjectures:                            1
% 1.30/1.01  epr:                                    7
% 1.30/1.01  horn:                                   15
% 1.30/1.01  ground:                                 4
% 1.30/1.01  unary:                                  6
% 1.30/1.01  binary:                                 8
% 1.30/1.01  lits:                                   34
% 1.30/1.01  lits_eq:                                6
% 1.30/1.01  fd_pure:                                0
% 1.30/1.01  fd_pseudo:                              0
% 1.30/1.01  fd_cond:                                3
% 1.30/1.01  fd_pseudo_cond:                         1
% 1.30/1.01  ac_symbols:                             0
% 1.30/1.01  
% 1.30/1.01  ------ Propositional Solver
% 1.30/1.01  
% 1.30/1.01  prop_solver_calls:                      28
% 1.30/1.01  prop_fast_solver_calls:                 783
% 1.30/1.01  smt_solver_calls:                       0
% 1.30/1.01  smt_fast_solver_calls:                  0
% 1.30/1.01  prop_num_of_clauses:                    1172
% 1.30/1.01  prop_preprocess_simplified:             4124
% 1.30/1.01  prop_fo_subsumed:                       34
% 1.30/1.01  prop_solver_time:                       0.
% 1.30/1.01  smt_solver_time:                        0.
% 1.30/1.01  smt_fast_solver_time:                   0.
% 1.30/1.01  prop_fast_solver_time:                  0.
% 1.30/1.01  prop_unsat_core_time:                   0.
% 1.30/1.01  
% 1.30/1.01  ------ QBF
% 1.30/1.01  
% 1.30/1.01  qbf_q_res:                              0
% 1.30/1.01  qbf_num_tautologies:                    0
% 1.30/1.01  qbf_prep_cycles:                        0
% 1.30/1.01  
% 1.30/1.01  ------ BMC1
% 1.30/1.01  
% 1.30/1.01  bmc1_current_bound:                     -1
% 1.30/1.01  bmc1_last_solved_bound:                 -1
% 1.30/1.01  bmc1_unsat_core_size:                   -1
% 1.30/1.01  bmc1_unsat_core_parents_size:           -1
% 1.30/1.01  bmc1_merge_next_fun:                    0
% 1.30/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.30/1.01  
% 1.30/1.01  ------ Instantiation
% 1.30/1.01  
% 1.30/1.01  inst_num_of_clauses:                    307
% 1.30/1.01  inst_num_in_passive:                    52
% 1.30/1.01  inst_num_in_active:                     202
% 1.30/1.01  inst_num_in_unprocessed:                53
% 1.30/1.01  inst_num_of_loops:                      240
% 1.30/1.01  inst_num_of_learning_restarts:          0
% 1.30/1.01  inst_num_moves_active_passive:          34
% 1.30/1.01  inst_lit_activity:                      0
% 1.30/1.01  inst_lit_activity_moves:                0
% 1.30/1.01  inst_num_tautologies:                   0
% 1.30/1.01  inst_num_prop_implied:                  0
% 1.30/1.01  inst_num_existing_simplified:           0
% 1.30/1.01  inst_num_eq_res_simplified:             0
% 1.30/1.01  inst_num_child_elim:                    0
% 1.30/1.01  inst_num_of_dismatching_blockings:      67
% 1.30/1.01  inst_num_of_non_proper_insts:           311
% 1.30/1.01  inst_num_of_duplicates:                 0
% 1.30/1.01  inst_inst_num_from_inst_to_res:         0
% 1.30/1.01  inst_dismatching_checking_time:         0.
% 1.30/1.01  
% 1.30/1.01  ------ Resolution
% 1.30/1.01  
% 1.30/1.01  res_num_of_clauses:                     0
% 1.30/1.01  res_num_in_passive:                     0
% 1.30/1.01  res_num_in_active:                      0
% 1.30/1.01  res_num_of_loops:                       105
% 1.30/1.01  res_forward_subset_subsumed:            26
% 1.30/1.01  res_backward_subset_subsumed:           0
% 1.30/1.01  res_forward_subsumed:                   0
% 1.30/1.01  res_backward_subsumed:                  0
% 1.30/1.01  res_forward_subsumption_resolution:     0
% 1.30/1.01  res_backward_subsumption_resolution:    0
% 1.30/1.01  res_clause_to_clause_subsumption:       155
% 1.30/1.01  res_orphan_elimination:                 0
% 1.30/1.01  res_tautology_del:                      40
% 1.30/1.01  res_num_eq_res_simplified:              6
% 1.30/1.01  res_num_sel_changes:                    0
% 1.30/1.01  res_moves_from_active_to_pass:          0
% 1.30/1.01  
% 1.30/1.01  ------ Superposition
% 1.30/1.01  
% 1.30/1.01  sup_time_total:                         0.
% 1.30/1.01  sup_time_generating:                    0.
% 1.30/1.01  sup_time_sim_full:                      0.
% 1.30/1.01  sup_time_sim_immed:                     0.
% 1.30/1.01  
% 1.30/1.01  sup_num_of_clauses:                     49
% 1.30/1.01  sup_num_in_active:                      41
% 1.30/1.01  sup_num_in_passive:                     8
% 1.30/1.01  sup_num_of_loops:                       47
% 1.30/1.01  sup_fw_superposition:                   43
% 1.30/1.01  sup_bw_superposition:                   20
% 1.30/1.01  sup_immediate_simplified:               11
% 1.30/1.01  sup_given_eliminated:                   1
% 1.30/1.01  comparisons_done:                       0
% 1.30/1.01  comparisons_avoided:                    0
% 1.30/1.01  
% 1.30/1.01  ------ Simplifications
% 1.30/1.01  
% 1.30/1.01  
% 1.30/1.01  sim_fw_subset_subsumed:                 4
% 1.30/1.01  sim_bw_subset_subsumed:                 4
% 1.30/1.01  sim_fw_subsumed:                        3
% 1.30/1.01  sim_bw_subsumed:                        0
% 1.30/1.01  sim_fw_subsumption_res:                 0
% 1.30/1.01  sim_bw_subsumption_res:                 0
% 1.30/1.01  sim_tautology_del:                      3
% 1.30/1.01  sim_eq_tautology_del:                   5
% 1.30/1.01  sim_eq_res_simp:                        0
% 1.30/1.01  sim_fw_demodulated:                     1
% 1.30/1.01  sim_bw_demodulated:                     6
% 1.30/1.01  sim_light_normalised:                   4
% 1.30/1.01  sim_joinable_taut:                      0
% 1.30/1.01  sim_joinable_simp:                      0
% 1.30/1.01  sim_ac_normalised:                      0
% 1.30/1.01  sim_smt_subsumption:                    0
% 1.30/1.01  
%------------------------------------------------------------------------------
