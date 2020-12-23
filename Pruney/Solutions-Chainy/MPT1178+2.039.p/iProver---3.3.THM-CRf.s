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
% DateTime   : Thu Dec  3 12:13:05 EST 2020

% Result     : Theorem 1.24s
% Output     : CNFRefutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 312 expanded)
%              Number of clauses        :   49 (  74 expanded)
%              Number of leaves         :   12 (  86 expanded)
%              Depth                    :   20
%              Number of atoms          :  436 (1819 expanded)
%              Number of equality atoms :   63 ( 286 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
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
             => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,conjecture,(
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

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
     => ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,sK3))
        & m1_orders_1(sK3,k1_orders_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
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
          ( k1_xboole_0 = k3_tarski(k4_orders_2(sK2,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK2))) )
      & l1_orders_2(sK2)
      & v5_orders_2(sK2)
      & v4_orders_2(sK2)
      & v3_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK2,sK3))
    & m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2)))
    & l1_orders_2(sK2)
    & v5_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f22,f30,f29])).

fof(f47,plain,(
    m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f31])).

fof(f46,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f42,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f43,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f44,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m2_orders_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
     => m2_orders_2(sK1(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m2_orders_2(sK1(X0,X1),X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f27])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m2_orders_2(sK1(X0,X1),X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
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

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ m2_orders_2(X3,X0,X1)
            | ~ r2_hidden(X3,X2) )
          & ( m2_orders_2(X3,X0,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ m2_orders_2(sK0(X0,X1,X2),X0,X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( m2_orders_2(sK0(X0,X1,X2),X0,X1)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ( ( ~ m2_orders_2(sK0(X0,X1,X2),X0,X1)
                    | ~ r2_hidden(sK0(X0,X1,X2),X2) )
                  & ( m2_orders_2(sK0(X0,X1,X2),X0,X1)
                    | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f37,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_orders_2(X0,X1))
      | ~ m2_orders_2(X4,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f48,plain,(
    k1_xboole_0 = k3_tarski(k4_orders_2(sK2,sK3)) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f12])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_9,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_11,negated_conjecture,
    ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_327,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK2))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_11])).

cnf(c_328,plain,
    ( ~ m2_orders_2(X0,X1,sK3)
    | r2_hidden(k1_funct_1(sK3,u1_struct_0(X1)),X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_12,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_514,plain,
    ( ~ m2_orders_2(X0,X1,sK3)
    | r2_hidden(k1_funct_1(sK3,u1_struct_0(X1)),X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK2))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_328,c_12])).

cnf(c_515,plain,
    ( ~ m2_orders_2(X0,sK2,sK3)
    | r2_hidden(k1_funct_1(sK3,u1_struct_0(sK2)),X0)
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | k1_orders_1(u1_struct_0(sK2)) != k1_orders_1(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_514])).

cnf(c_16,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_15,negated_conjecture,
    ( v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_14,negated_conjecture,
    ( v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_13,negated_conjecture,
    ( v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_519,plain,
    ( ~ m2_orders_2(X0,sK2,sK3)
    | r2_hidden(k1_funct_1(sK3,u1_struct_0(sK2)),X0)
    | k1_orders_1(u1_struct_0(sK2)) != k1_orders_1(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_515,c_16,c_15,c_14,c_13])).

cnf(c_757,plain,
    ( ~ m2_orders_2(X0,sK2,sK3)
    | r2_hidden(k1_funct_1(sK3,u1_struct_0(sK2)),X0) ),
    inference(equality_resolution_simp,[status(thm)],[c_519])).

cnf(c_1171,plain,
    ( m2_orders_2(X0,sK2,sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK3,u1_struct_0(sK2)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_757])).

cnf(c_8,plain,
    ( m2_orders_2(sK1(X0,X1),X0,X1)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_234,plain,
    ( m2_orders_2(sK1(X0,X1),X0,X1)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK2))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_11])).

cnf(c_235,plain,
    ( m2_orders_2(sK1(X0,sK3),X0,sK3)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_234])).

cnf(c_583,plain,
    ( m2_orders_2(sK1(X0,sK3),X0,sK3)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK2))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_235,c_12])).

cnf(c_584,plain,
    ( m2_orders_2(sK1(sK2,sK3),sK2,sK3)
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | k1_orders_1(u1_struct_0(sK2)) != k1_orders_1(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_583])).

cnf(c_586,plain,
    ( m2_orders_2(sK1(sK2,sK3),sK2,sK3)
    | k1_orders_1(u1_struct_0(sK2)) != k1_orders_1(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_584,c_16,c_15,c_14,c_13])).

cnf(c_747,plain,
    ( m2_orders_2(sK1(sK2,sK3),sK2,sK3) ),
    inference(equality_resolution_simp,[status(thm)],[c_586])).

cnf(c_1174,plain,
    ( m2_orders_2(sK1(sK2,sK3),sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_747])).

cnf(c_6,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | r2_hidden(X0,k4_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_387,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | r2_hidden(X0,k4_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK2))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_11])).

cnf(c_388,plain,
    ( ~ m2_orders_2(X0,X1,sK3)
    | r2_hidden(X0,k4_orders_2(X1,sK3))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_387])).

cnf(c_472,plain,
    ( ~ m2_orders_2(X0,X1,sK3)
    | r2_hidden(X0,k4_orders_2(X1,sK3))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK2))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_388,c_12])).

cnf(c_473,plain,
    ( ~ m2_orders_2(X0,sK2,sK3)
    | r2_hidden(X0,k4_orders_2(sK2,sK3))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | k1_orders_1(u1_struct_0(sK2)) != k1_orders_1(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_472])).

cnf(c_477,plain,
    ( ~ m2_orders_2(X0,sK2,sK3)
    | r2_hidden(X0,k4_orders_2(sK2,sK3))
    | k1_orders_1(u1_struct_0(sK2)) != k1_orders_1(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_473,c_16,c_15,c_14,c_13])).

cnf(c_765,plain,
    ( ~ m2_orders_2(X0,sK2,sK3)
    | r2_hidden(X0,k4_orders_2(sK2,sK3)) ),
    inference(equality_resolution_simp,[status(thm)],[c_477])).

cnf(c_782,plain,
    ( ~ m2_orders_2(X0,sK2,sK3)
    | r2_hidden(X0,k4_orders_2(sK2,sK3)) ),
    inference(prop_impl,[status(thm)],[c_765])).

cnf(c_1169,plain,
    ( m2_orders_2(X0,sK2,sK3) != iProver_top
    | r2_hidden(X0,k4_orders_2(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_782])).

cnf(c_10,negated_conjecture,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK2,sK3)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_3,plain,
    ( r1_tarski(X0,k3_tarski(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_185,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_2])).

cnf(c_186,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_185])).

cnf(c_200,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | ~ r2_hidden(X1,X2)
    | X0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_186])).

cnf(c_201,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | ~ r2_hidden(X1,X0) ),
    inference(unflattening,[status(thm)],[c_200])).

cnf(c_215,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | X3 != X0
    | k3_tarski(X1) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_201])).

cnf(c_216,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X0)
    | k3_tarski(X1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_215])).

cnf(c_1175,plain,
    ( k3_tarski(X0) != k1_xboole_0
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_216])).

cnf(c_1414,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X1,k4_orders_2(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_1175])).

cnf(c_1471,plain,
    ( m2_orders_2(X0,sK2,sK3) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1169,c_1414])).

cnf(c_1491,plain,
    ( r2_hidden(X0,sK1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1174,c_1471])).

cnf(c_1626,plain,
    ( m2_orders_2(sK1(sK2,sK3),sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1171,c_1491])).

cnf(c_748,plain,
    ( m2_orders_2(sK1(sK2,sK3),sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_747])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1626,c_748])).

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
% 0.12/0.34  % DateTime   : Tue Dec  1 14:28:52 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 1.24/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.24/1.00  
% 1.24/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.24/1.00  
% 1.24/1.00  ------  iProver source info
% 1.24/1.00  
% 1.24/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.24/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.24/1.00  git: non_committed_changes: false
% 1.24/1.00  git: last_make_outside_of_git: false
% 1.24/1.00  
% 1.24/1.00  ------ 
% 1.24/1.00  
% 1.24/1.00  ------ Input Options
% 1.24/1.00  
% 1.24/1.00  --out_options                           all
% 1.24/1.00  --tptp_safe_out                         true
% 1.24/1.00  --problem_path                          ""
% 1.24/1.00  --include_path                          ""
% 1.24/1.00  --clausifier                            res/vclausify_rel
% 1.24/1.00  --clausifier_options                    --mode clausify
% 1.24/1.00  --stdin                                 false
% 1.24/1.00  --stats_out                             all
% 1.24/1.00  
% 1.24/1.00  ------ General Options
% 1.24/1.00  
% 1.24/1.00  --fof                                   false
% 1.24/1.00  --time_out_real                         305.
% 1.24/1.00  --time_out_virtual                      -1.
% 1.24/1.00  --symbol_type_check                     false
% 1.24/1.00  --clausify_out                          false
% 1.24/1.00  --sig_cnt_out                           false
% 1.24/1.00  --trig_cnt_out                          false
% 1.24/1.00  --trig_cnt_out_tolerance                1.
% 1.24/1.00  --trig_cnt_out_sk_spl                   false
% 1.24/1.00  --abstr_cl_out                          false
% 1.24/1.00  
% 1.24/1.00  ------ Global Options
% 1.24/1.00  
% 1.24/1.00  --schedule                              default
% 1.24/1.00  --add_important_lit                     false
% 1.24/1.00  --prop_solver_per_cl                    1000
% 1.24/1.00  --min_unsat_core                        false
% 1.24/1.00  --soft_assumptions                      false
% 1.24/1.00  --soft_lemma_size                       3
% 1.24/1.00  --prop_impl_unit_size                   0
% 1.24/1.00  --prop_impl_unit                        []
% 1.24/1.00  --share_sel_clauses                     true
% 1.24/1.00  --reset_solvers                         false
% 1.24/1.00  --bc_imp_inh                            [conj_cone]
% 1.24/1.00  --conj_cone_tolerance                   3.
% 1.24/1.00  --extra_neg_conj                        none
% 1.24/1.00  --large_theory_mode                     true
% 1.24/1.00  --prolific_symb_bound                   200
% 1.24/1.00  --lt_threshold                          2000
% 1.24/1.00  --clause_weak_htbl                      true
% 1.24/1.00  --gc_record_bc_elim                     false
% 1.24/1.00  
% 1.24/1.00  ------ Preprocessing Options
% 1.24/1.00  
% 1.24/1.00  --preprocessing_flag                    true
% 1.24/1.00  --time_out_prep_mult                    0.1
% 1.24/1.00  --splitting_mode                        input
% 1.24/1.00  --splitting_grd                         true
% 1.24/1.00  --splitting_cvd                         false
% 1.24/1.00  --splitting_cvd_svl                     false
% 1.24/1.00  --splitting_nvd                         32
% 1.24/1.00  --sub_typing                            true
% 1.24/1.00  --prep_gs_sim                           true
% 1.24/1.00  --prep_unflatten                        true
% 1.24/1.00  --prep_res_sim                          true
% 1.24/1.00  --prep_upred                            true
% 1.24/1.00  --prep_sem_filter                       exhaustive
% 1.24/1.00  --prep_sem_filter_out                   false
% 1.24/1.00  --pred_elim                             true
% 1.24/1.00  --res_sim_input                         true
% 1.24/1.00  --eq_ax_congr_red                       true
% 1.24/1.00  --pure_diseq_elim                       true
% 1.24/1.00  --brand_transform                       false
% 1.24/1.00  --non_eq_to_eq                          false
% 1.24/1.00  --prep_def_merge                        true
% 1.24/1.00  --prep_def_merge_prop_impl              false
% 1.24/1.00  --prep_def_merge_mbd                    true
% 1.24/1.00  --prep_def_merge_tr_red                 false
% 1.24/1.00  --prep_def_merge_tr_cl                  false
% 1.24/1.00  --smt_preprocessing                     true
% 1.24/1.00  --smt_ac_axioms                         fast
% 1.24/1.00  --preprocessed_out                      false
% 1.24/1.00  --preprocessed_stats                    false
% 1.24/1.00  
% 1.24/1.00  ------ Abstraction refinement Options
% 1.24/1.00  
% 1.24/1.00  --abstr_ref                             []
% 1.24/1.00  --abstr_ref_prep                        false
% 1.24/1.00  --abstr_ref_until_sat                   false
% 1.24/1.00  --abstr_ref_sig_restrict                funpre
% 1.24/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.24/1.00  --abstr_ref_under                       []
% 1.24/1.00  
% 1.24/1.00  ------ SAT Options
% 1.24/1.00  
% 1.24/1.00  --sat_mode                              false
% 1.24/1.00  --sat_fm_restart_options                ""
% 1.24/1.00  --sat_gr_def                            false
% 1.24/1.00  --sat_epr_types                         true
% 1.24/1.00  --sat_non_cyclic_types                  false
% 1.24/1.00  --sat_finite_models                     false
% 1.24/1.00  --sat_fm_lemmas                         false
% 1.24/1.00  --sat_fm_prep                           false
% 1.24/1.00  --sat_fm_uc_incr                        true
% 1.24/1.00  --sat_out_model                         small
% 1.24/1.00  --sat_out_clauses                       false
% 1.24/1.00  
% 1.24/1.00  ------ QBF Options
% 1.24/1.00  
% 1.24/1.00  --qbf_mode                              false
% 1.24/1.00  --qbf_elim_univ                         false
% 1.24/1.00  --qbf_dom_inst                          none
% 1.24/1.00  --qbf_dom_pre_inst                      false
% 1.24/1.00  --qbf_sk_in                             false
% 1.24/1.00  --qbf_pred_elim                         true
% 1.24/1.00  --qbf_split                             512
% 1.24/1.00  
% 1.24/1.00  ------ BMC1 Options
% 1.24/1.00  
% 1.24/1.00  --bmc1_incremental                      false
% 1.24/1.00  --bmc1_axioms                           reachable_all
% 1.24/1.00  --bmc1_min_bound                        0
% 1.24/1.00  --bmc1_max_bound                        -1
% 1.24/1.00  --bmc1_max_bound_default                -1
% 1.24/1.00  --bmc1_symbol_reachability              true
% 1.24/1.00  --bmc1_property_lemmas                  false
% 1.24/1.00  --bmc1_k_induction                      false
% 1.24/1.00  --bmc1_non_equiv_states                 false
% 1.24/1.00  --bmc1_deadlock                         false
% 1.24/1.00  --bmc1_ucm                              false
% 1.24/1.00  --bmc1_add_unsat_core                   none
% 1.24/1.00  --bmc1_unsat_core_children              false
% 1.24/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.24/1.00  --bmc1_out_stat                         full
% 1.24/1.00  --bmc1_ground_init                      false
% 1.24/1.00  --bmc1_pre_inst_next_state              false
% 1.24/1.00  --bmc1_pre_inst_state                   false
% 1.24/1.00  --bmc1_pre_inst_reach_state             false
% 1.24/1.00  --bmc1_out_unsat_core                   false
% 1.24/1.00  --bmc1_aig_witness_out                  false
% 1.24/1.00  --bmc1_verbose                          false
% 1.24/1.00  --bmc1_dump_clauses_tptp                false
% 1.24/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.24/1.00  --bmc1_dump_file                        -
% 1.24/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.24/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.24/1.00  --bmc1_ucm_extend_mode                  1
% 1.24/1.00  --bmc1_ucm_init_mode                    2
% 1.24/1.00  --bmc1_ucm_cone_mode                    none
% 1.24/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.24/1.00  --bmc1_ucm_relax_model                  4
% 1.24/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.24/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.24/1.00  --bmc1_ucm_layered_model                none
% 1.24/1.00  --bmc1_ucm_max_lemma_size               10
% 1.24/1.00  
% 1.24/1.00  ------ AIG Options
% 1.24/1.00  
% 1.24/1.00  --aig_mode                              false
% 1.24/1.00  
% 1.24/1.00  ------ Instantiation Options
% 1.24/1.00  
% 1.24/1.00  --instantiation_flag                    true
% 1.24/1.00  --inst_sos_flag                         false
% 1.24/1.00  --inst_sos_phase                        true
% 1.24/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.24/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.24/1.00  --inst_lit_sel_side                     num_symb
% 1.24/1.00  --inst_solver_per_active                1400
% 1.24/1.00  --inst_solver_calls_frac                1.
% 1.24/1.00  --inst_passive_queue_type               priority_queues
% 1.24/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.24/1.00  --inst_passive_queues_freq              [25;2]
% 1.24/1.00  --inst_dismatching                      true
% 1.24/1.00  --inst_eager_unprocessed_to_passive     true
% 1.24/1.00  --inst_prop_sim_given                   true
% 1.24/1.00  --inst_prop_sim_new                     false
% 1.24/1.00  --inst_subs_new                         false
% 1.24/1.00  --inst_eq_res_simp                      false
% 1.24/1.00  --inst_subs_given                       false
% 1.24/1.00  --inst_orphan_elimination               true
% 1.24/1.00  --inst_learning_loop_flag               true
% 1.24/1.00  --inst_learning_start                   3000
% 1.24/1.00  --inst_learning_factor                  2
% 1.24/1.00  --inst_start_prop_sim_after_learn       3
% 1.24/1.00  --inst_sel_renew                        solver
% 1.24/1.00  --inst_lit_activity_flag                true
% 1.24/1.00  --inst_restr_to_given                   false
% 1.24/1.00  --inst_activity_threshold               500
% 1.24/1.00  --inst_out_proof                        true
% 1.24/1.00  
% 1.24/1.00  ------ Resolution Options
% 1.24/1.00  
% 1.24/1.00  --resolution_flag                       true
% 1.24/1.00  --res_lit_sel                           adaptive
% 1.24/1.00  --res_lit_sel_side                      none
% 1.24/1.00  --res_ordering                          kbo
% 1.24/1.00  --res_to_prop_solver                    active
% 1.24/1.00  --res_prop_simpl_new                    false
% 1.24/1.00  --res_prop_simpl_given                  true
% 1.24/1.00  --res_passive_queue_type                priority_queues
% 1.24/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.24/1.00  --res_passive_queues_freq               [15;5]
% 1.24/1.00  --res_forward_subs                      full
% 1.24/1.00  --res_backward_subs                     full
% 1.24/1.00  --res_forward_subs_resolution           true
% 1.24/1.00  --res_backward_subs_resolution          true
% 1.24/1.00  --res_orphan_elimination                true
% 1.24/1.00  --res_time_limit                        2.
% 1.24/1.00  --res_out_proof                         true
% 1.24/1.00  
% 1.24/1.00  ------ Superposition Options
% 1.24/1.00  
% 1.24/1.00  --superposition_flag                    true
% 1.24/1.00  --sup_passive_queue_type                priority_queues
% 1.24/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.24/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.24/1.00  --demod_completeness_check              fast
% 1.24/1.00  --demod_use_ground                      true
% 1.24/1.00  --sup_to_prop_solver                    passive
% 1.24/1.00  --sup_prop_simpl_new                    true
% 1.24/1.00  --sup_prop_simpl_given                  true
% 1.24/1.00  --sup_fun_splitting                     false
% 1.24/1.00  --sup_smt_interval                      50000
% 1.24/1.00  
% 1.24/1.00  ------ Superposition Simplification Setup
% 1.24/1.00  
% 1.24/1.00  --sup_indices_passive                   []
% 1.24/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.24/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.24/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.24/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.24/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.24/1.00  --sup_full_bw                           [BwDemod]
% 1.24/1.00  --sup_immed_triv                        [TrivRules]
% 1.24/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.24/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.24/1.00  --sup_immed_bw_main                     []
% 1.24/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.24/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.24/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.24/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.24/1.00  
% 1.24/1.00  ------ Combination Options
% 1.24/1.00  
% 1.24/1.00  --comb_res_mult                         3
% 1.24/1.00  --comb_sup_mult                         2
% 1.24/1.00  --comb_inst_mult                        10
% 1.24/1.00  
% 1.24/1.00  ------ Debug Options
% 1.24/1.00  
% 1.24/1.00  --dbg_backtrace                         false
% 1.24/1.00  --dbg_dump_prop_clauses                 false
% 1.24/1.00  --dbg_dump_prop_clauses_file            -
% 1.24/1.00  --dbg_out_stat                          false
% 1.24/1.00  ------ Parsing...
% 1.24/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.24/1.00  
% 1.24/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 1.24/1.00  
% 1.24/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.24/1.00  
% 1.24/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.24/1.00  ------ Proving...
% 1.24/1.00  ------ Problem Properties 
% 1.24/1.00  
% 1.24/1.00  
% 1.24/1.00  clauses                                 8
% 1.24/1.00  conjectures                             1
% 1.24/1.00  EPR                                     0
% 1.24/1.00  Horn                                    7
% 1.24/1.00  unary                                   2
% 1.24/1.00  binary                                  3
% 1.24/1.00  lits                                    17
% 1.24/1.00  lits eq                                 4
% 1.24/1.00  fd_pure                                 0
% 1.24/1.00  fd_pseudo                               0
% 1.24/1.00  fd_cond                                 2
% 1.24/1.00  fd_pseudo_cond                          0
% 1.24/1.00  AC symbols                              0
% 1.24/1.00  
% 1.24/1.00  ------ Schedule dynamic 5 is on 
% 1.24/1.00  
% 1.24/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.24/1.00  
% 1.24/1.00  
% 1.24/1.00  ------ 
% 1.24/1.00  Current options:
% 1.24/1.00  ------ 
% 1.24/1.00  
% 1.24/1.00  ------ Input Options
% 1.24/1.00  
% 1.24/1.00  --out_options                           all
% 1.24/1.00  --tptp_safe_out                         true
% 1.24/1.00  --problem_path                          ""
% 1.24/1.00  --include_path                          ""
% 1.24/1.00  --clausifier                            res/vclausify_rel
% 1.24/1.00  --clausifier_options                    --mode clausify
% 1.24/1.00  --stdin                                 false
% 1.24/1.00  --stats_out                             all
% 1.24/1.00  
% 1.24/1.00  ------ General Options
% 1.24/1.00  
% 1.24/1.00  --fof                                   false
% 1.24/1.00  --time_out_real                         305.
% 1.24/1.00  --time_out_virtual                      -1.
% 1.24/1.00  --symbol_type_check                     false
% 1.24/1.00  --clausify_out                          false
% 1.24/1.00  --sig_cnt_out                           false
% 1.24/1.00  --trig_cnt_out                          false
% 1.24/1.00  --trig_cnt_out_tolerance                1.
% 1.24/1.00  --trig_cnt_out_sk_spl                   false
% 1.24/1.00  --abstr_cl_out                          false
% 1.24/1.00  
% 1.24/1.00  ------ Global Options
% 1.24/1.00  
% 1.24/1.00  --schedule                              default
% 1.24/1.00  --add_important_lit                     false
% 1.24/1.00  --prop_solver_per_cl                    1000
% 1.24/1.00  --min_unsat_core                        false
% 1.24/1.00  --soft_assumptions                      false
% 1.24/1.00  --soft_lemma_size                       3
% 1.24/1.00  --prop_impl_unit_size                   0
% 1.24/1.00  --prop_impl_unit                        []
% 1.24/1.00  --share_sel_clauses                     true
% 1.24/1.00  --reset_solvers                         false
% 1.24/1.00  --bc_imp_inh                            [conj_cone]
% 1.24/1.00  --conj_cone_tolerance                   3.
% 1.24/1.00  --extra_neg_conj                        none
% 1.24/1.00  --large_theory_mode                     true
% 1.24/1.00  --prolific_symb_bound                   200
% 1.24/1.00  --lt_threshold                          2000
% 1.24/1.00  --clause_weak_htbl                      true
% 1.24/1.00  --gc_record_bc_elim                     false
% 1.24/1.00  
% 1.24/1.00  ------ Preprocessing Options
% 1.24/1.00  
% 1.24/1.00  --preprocessing_flag                    true
% 1.24/1.00  --time_out_prep_mult                    0.1
% 1.24/1.00  --splitting_mode                        input
% 1.24/1.00  --splitting_grd                         true
% 1.24/1.00  --splitting_cvd                         false
% 1.24/1.00  --splitting_cvd_svl                     false
% 1.24/1.00  --splitting_nvd                         32
% 1.24/1.00  --sub_typing                            true
% 1.24/1.00  --prep_gs_sim                           true
% 1.24/1.00  --prep_unflatten                        true
% 1.24/1.00  --prep_res_sim                          true
% 1.24/1.00  --prep_upred                            true
% 1.24/1.00  --prep_sem_filter                       exhaustive
% 1.24/1.00  --prep_sem_filter_out                   false
% 1.24/1.00  --pred_elim                             true
% 1.24/1.00  --res_sim_input                         true
% 1.24/1.00  --eq_ax_congr_red                       true
% 1.24/1.00  --pure_diseq_elim                       true
% 1.24/1.00  --brand_transform                       false
% 1.24/1.00  --non_eq_to_eq                          false
% 1.24/1.00  --prep_def_merge                        true
% 1.24/1.00  --prep_def_merge_prop_impl              false
% 1.24/1.00  --prep_def_merge_mbd                    true
% 1.24/1.00  --prep_def_merge_tr_red                 false
% 1.24/1.00  --prep_def_merge_tr_cl                  false
% 1.24/1.00  --smt_preprocessing                     true
% 1.24/1.00  --smt_ac_axioms                         fast
% 1.24/1.00  --preprocessed_out                      false
% 1.24/1.00  --preprocessed_stats                    false
% 1.24/1.00  
% 1.24/1.00  ------ Abstraction refinement Options
% 1.24/1.00  
% 1.24/1.00  --abstr_ref                             []
% 1.24/1.00  --abstr_ref_prep                        false
% 1.24/1.00  --abstr_ref_until_sat                   false
% 1.24/1.00  --abstr_ref_sig_restrict                funpre
% 1.24/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.24/1.00  --abstr_ref_under                       []
% 1.24/1.00  
% 1.24/1.00  ------ SAT Options
% 1.24/1.00  
% 1.24/1.00  --sat_mode                              false
% 1.24/1.00  --sat_fm_restart_options                ""
% 1.24/1.00  --sat_gr_def                            false
% 1.24/1.00  --sat_epr_types                         true
% 1.24/1.00  --sat_non_cyclic_types                  false
% 1.24/1.00  --sat_finite_models                     false
% 1.24/1.00  --sat_fm_lemmas                         false
% 1.24/1.00  --sat_fm_prep                           false
% 1.24/1.00  --sat_fm_uc_incr                        true
% 1.24/1.00  --sat_out_model                         small
% 1.24/1.00  --sat_out_clauses                       false
% 1.24/1.00  
% 1.24/1.00  ------ QBF Options
% 1.24/1.00  
% 1.24/1.00  --qbf_mode                              false
% 1.24/1.00  --qbf_elim_univ                         false
% 1.24/1.00  --qbf_dom_inst                          none
% 1.24/1.00  --qbf_dom_pre_inst                      false
% 1.24/1.00  --qbf_sk_in                             false
% 1.24/1.00  --qbf_pred_elim                         true
% 1.24/1.00  --qbf_split                             512
% 1.24/1.00  
% 1.24/1.00  ------ BMC1 Options
% 1.24/1.00  
% 1.24/1.00  --bmc1_incremental                      false
% 1.24/1.00  --bmc1_axioms                           reachable_all
% 1.24/1.00  --bmc1_min_bound                        0
% 1.24/1.00  --bmc1_max_bound                        -1
% 1.24/1.00  --bmc1_max_bound_default                -1
% 1.24/1.00  --bmc1_symbol_reachability              true
% 1.24/1.00  --bmc1_property_lemmas                  false
% 1.24/1.00  --bmc1_k_induction                      false
% 1.24/1.00  --bmc1_non_equiv_states                 false
% 1.24/1.00  --bmc1_deadlock                         false
% 1.24/1.00  --bmc1_ucm                              false
% 1.24/1.00  --bmc1_add_unsat_core                   none
% 1.24/1.00  --bmc1_unsat_core_children              false
% 1.24/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.24/1.00  --bmc1_out_stat                         full
% 1.24/1.00  --bmc1_ground_init                      false
% 1.24/1.00  --bmc1_pre_inst_next_state              false
% 1.24/1.00  --bmc1_pre_inst_state                   false
% 1.24/1.00  --bmc1_pre_inst_reach_state             false
% 1.24/1.00  --bmc1_out_unsat_core                   false
% 1.24/1.00  --bmc1_aig_witness_out                  false
% 1.24/1.00  --bmc1_verbose                          false
% 1.24/1.00  --bmc1_dump_clauses_tptp                false
% 1.24/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.24/1.00  --bmc1_dump_file                        -
% 1.24/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.24/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.24/1.00  --bmc1_ucm_extend_mode                  1
% 1.24/1.01  --bmc1_ucm_init_mode                    2
% 1.24/1.01  --bmc1_ucm_cone_mode                    none
% 1.24/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.24/1.01  --bmc1_ucm_relax_model                  4
% 1.24/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.24/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.24/1.01  --bmc1_ucm_layered_model                none
% 1.24/1.01  --bmc1_ucm_max_lemma_size               10
% 1.24/1.01  
% 1.24/1.01  ------ AIG Options
% 1.24/1.01  
% 1.24/1.01  --aig_mode                              false
% 1.24/1.01  
% 1.24/1.01  ------ Instantiation Options
% 1.24/1.01  
% 1.24/1.01  --instantiation_flag                    true
% 1.24/1.01  --inst_sos_flag                         false
% 1.24/1.01  --inst_sos_phase                        true
% 1.24/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.24/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.24/1.01  --inst_lit_sel_side                     none
% 1.24/1.01  --inst_solver_per_active                1400
% 1.24/1.01  --inst_solver_calls_frac                1.
% 1.24/1.01  --inst_passive_queue_type               priority_queues
% 1.24/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.24/1.01  --inst_passive_queues_freq              [25;2]
% 1.24/1.01  --inst_dismatching                      true
% 1.24/1.01  --inst_eager_unprocessed_to_passive     true
% 1.24/1.01  --inst_prop_sim_given                   true
% 1.24/1.01  --inst_prop_sim_new                     false
% 1.24/1.01  --inst_subs_new                         false
% 1.24/1.01  --inst_eq_res_simp                      false
% 1.24/1.01  --inst_subs_given                       false
% 1.24/1.01  --inst_orphan_elimination               true
% 1.24/1.01  --inst_learning_loop_flag               true
% 1.24/1.01  --inst_learning_start                   3000
% 1.24/1.01  --inst_learning_factor                  2
% 1.24/1.01  --inst_start_prop_sim_after_learn       3
% 1.24/1.01  --inst_sel_renew                        solver
% 1.24/1.01  --inst_lit_activity_flag                true
% 1.24/1.01  --inst_restr_to_given                   false
% 1.24/1.01  --inst_activity_threshold               500
% 1.24/1.01  --inst_out_proof                        true
% 1.24/1.01  
% 1.24/1.01  ------ Resolution Options
% 1.24/1.01  
% 1.24/1.01  --resolution_flag                       false
% 1.24/1.01  --res_lit_sel                           adaptive
% 1.24/1.01  --res_lit_sel_side                      none
% 1.24/1.01  --res_ordering                          kbo
% 1.24/1.01  --res_to_prop_solver                    active
% 1.24/1.01  --res_prop_simpl_new                    false
% 1.24/1.01  --res_prop_simpl_given                  true
% 1.24/1.01  --res_passive_queue_type                priority_queues
% 1.24/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.24/1.01  --res_passive_queues_freq               [15;5]
% 1.24/1.01  --res_forward_subs                      full
% 1.24/1.01  --res_backward_subs                     full
% 1.24/1.01  --res_forward_subs_resolution           true
% 1.24/1.01  --res_backward_subs_resolution          true
% 1.24/1.01  --res_orphan_elimination                true
% 1.24/1.01  --res_time_limit                        2.
% 1.24/1.01  --res_out_proof                         true
% 1.24/1.01  
% 1.24/1.01  ------ Superposition Options
% 1.24/1.01  
% 1.24/1.01  --superposition_flag                    true
% 1.24/1.01  --sup_passive_queue_type                priority_queues
% 1.24/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.24/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.24/1.01  --demod_completeness_check              fast
% 1.24/1.01  --demod_use_ground                      true
% 1.24/1.01  --sup_to_prop_solver                    passive
% 1.24/1.01  --sup_prop_simpl_new                    true
% 1.24/1.01  --sup_prop_simpl_given                  true
% 1.24/1.01  --sup_fun_splitting                     false
% 1.24/1.01  --sup_smt_interval                      50000
% 1.24/1.01  
% 1.24/1.01  ------ Superposition Simplification Setup
% 1.24/1.01  
% 1.24/1.01  --sup_indices_passive                   []
% 1.24/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.24/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.24/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.24/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.24/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.24/1.01  --sup_full_bw                           [BwDemod]
% 1.24/1.01  --sup_immed_triv                        [TrivRules]
% 1.24/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.24/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.24/1.01  --sup_immed_bw_main                     []
% 1.24/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.24/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.24/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.24/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.24/1.01  
% 1.24/1.01  ------ Combination Options
% 1.24/1.01  
% 1.24/1.01  --comb_res_mult                         3
% 1.24/1.01  --comb_sup_mult                         2
% 1.24/1.01  --comb_inst_mult                        10
% 1.24/1.01  
% 1.24/1.01  ------ Debug Options
% 1.24/1.01  
% 1.24/1.01  --dbg_backtrace                         false
% 1.24/1.01  --dbg_dump_prop_clauses                 false
% 1.24/1.01  --dbg_dump_prop_clauses_file            -
% 1.24/1.01  --dbg_out_stat                          false
% 1.24/1.01  
% 1.24/1.01  
% 1.24/1.01  
% 1.24/1.01  
% 1.24/1.01  ------ Proving...
% 1.24/1.01  
% 1.24/1.01  
% 1.24/1.01  % SZS status Theorem for theBenchmark.p
% 1.24/1.01  
% 1.24/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 1.24/1.01  
% 1.24/1.01  fof(f7,axiom,(
% 1.24/1.01    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2))))),
% 1.24/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.24/1.01  
% 1.24/1.01  fof(f19,plain,(
% 1.24/1.01    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.24/1.01    inference(ennf_transformation,[],[f7])).
% 1.24/1.01  
% 1.24/1.01  fof(f20,plain,(
% 1.24/1.01    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.24/1.01    inference(flattening,[],[f19])).
% 1.24/1.01  
% 1.24/1.01  fof(f41,plain,(
% 1.24/1.01    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.24/1.01    inference(cnf_transformation,[],[f20])).
% 1.24/1.01  
% 1.24/1.01  fof(f8,conjecture,(
% 1.24/1.01    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 1.24/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.24/1.01  
% 1.24/1.01  fof(f9,negated_conjecture,(
% 1.24/1.01    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 1.24/1.01    inference(negated_conjecture,[],[f8])).
% 1.24/1.01  
% 1.24/1.01  fof(f21,plain,(
% 1.24/1.01    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.24/1.01    inference(ennf_transformation,[],[f9])).
% 1.24/1.01  
% 1.24/1.01  fof(f22,plain,(
% 1.24/1.01    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.24/1.01    inference(flattening,[],[f21])).
% 1.24/1.01  
% 1.24/1.01  fof(f30,plain,(
% 1.24/1.01    ( ! [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) => (k1_xboole_0 = k3_tarski(k4_orders_2(X0,sK3)) & m1_orders_1(sK3,k1_orders_1(u1_struct_0(X0))))) )),
% 1.24/1.01    introduced(choice_axiom,[])).
% 1.24/1.01  
% 1.24/1.01  fof(f29,plain,(
% 1.24/1.01    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(sK2,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK2)))) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2))),
% 1.24/1.01    introduced(choice_axiom,[])).
% 1.24/1.01  
% 1.24/1.01  fof(f31,plain,(
% 1.24/1.01    (k1_xboole_0 = k3_tarski(k4_orders_2(sK2,sK3)) & m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2)))) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2)),
% 1.24/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f22,f30,f29])).
% 1.24/1.01  
% 1.24/1.01  fof(f47,plain,(
% 1.24/1.01    m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2)))),
% 1.24/1.01    inference(cnf_transformation,[],[f31])).
% 1.24/1.01  
% 1.24/1.01  fof(f46,plain,(
% 1.24/1.01    l1_orders_2(sK2)),
% 1.24/1.01    inference(cnf_transformation,[],[f31])).
% 1.24/1.01  
% 1.24/1.01  fof(f42,plain,(
% 1.24/1.01    ~v2_struct_0(sK2)),
% 1.24/1.01    inference(cnf_transformation,[],[f31])).
% 1.24/1.01  
% 1.24/1.01  fof(f43,plain,(
% 1.24/1.01    v3_orders_2(sK2)),
% 1.24/1.01    inference(cnf_transformation,[],[f31])).
% 1.24/1.01  
% 1.24/1.01  fof(f44,plain,(
% 1.24/1.01    v4_orders_2(sK2)),
% 1.24/1.01    inference(cnf_transformation,[],[f31])).
% 1.24/1.01  
% 1.24/1.01  fof(f45,plain,(
% 1.24/1.01    v5_orders_2(sK2)),
% 1.24/1.01    inference(cnf_transformation,[],[f31])).
% 1.24/1.01  
% 1.24/1.01  fof(f6,axiom,(
% 1.24/1.01    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ? [X2] : m2_orders_2(X2,X0,X1))),
% 1.24/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.24/1.01  
% 1.24/1.01  fof(f17,plain,(
% 1.24/1.01    ! [X0,X1] : (? [X2] : m2_orders_2(X2,X0,X1) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.24/1.01    inference(ennf_transformation,[],[f6])).
% 1.24/1.01  
% 1.24/1.01  fof(f18,plain,(
% 1.24/1.01    ! [X0,X1] : (? [X2] : m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.24/1.01    inference(flattening,[],[f17])).
% 1.24/1.01  
% 1.24/1.01  fof(f27,plain,(
% 1.24/1.01    ! [X1,X0] : (? [X2] : m2_orders_2(X2,X0,X1) => m2_orders_2(sK1(X0,X1),X0,X1))),
% 1.24/1.01    introduced(choice_axiom,[])).
% 1.24/1.01  
% 1.24/1.01  fof(f28,plain,(
% 1.24/1.01    ! [X0,X1] : (m2_orders_2(sK1(X0,X1),X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.24/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f27])).
% 1.24/1.01  
% 1.24/1.01  fof(f40,plain,(
% 1.24/1.01    ( ! [X0,X1] : (m2_orders_2(sK1(X0,X1),X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.24/1.01    inference(cnf_transformation,[],[f28])).
% 1.24/1.01  
% 1.24/1.01  fof(f5,axiom,(
% 1.24/1.01    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1)))))),
% 1.24/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.24/1.01  
% 1.24/1.01  fof(f15,plain,(
% 1.24/1.01    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.24/1.01    inference(ennf_transformation,[],[f5])).
% 1.24/1.01  
% 1.24/1.01  fof(f16,plain,(
% 1.24/1.01    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.24/1.01    inference(flattening,[],[f15])).
% 1.24/1.01  
% 1.24/1.01  fof(f23,plain,(
% 1.24/1.01    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~m2_orders_2(X3,X0,X1)) & (m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.24/1.01    inference(nnf_transformation,[],[f16])).
% 1.24/1.01  
% 1.24/1.01  fof(f24,plain,(
% 1.24/1.01    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.24/1.01    inference(rectify,[],[f23])).
% 1.24/1.01  
% 1.24/1.01  fof(f25,plain,(
% 1.24/1.01    ! [X2,X1,X0] : (? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2))) => ((~m2_orders_2(sK0(X0,X1,X2),X0,X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (m2_orders_2(sK0(X0,X1,X2),X0,X1) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 1.24/1.01    introduced(choice_axiom,[])).
% 1.24/1.01  
% 1.24/1.01  fof(f26,plain,(
% 1.24/1.01    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ((~m2_orders_2(sK0(X0,X1,X2),X0,X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (m2_orders_2(sK0(X0,X1,X2),X0,X1) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.24/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 1.24/1.01  
% 1.24/1.01  fof(f37,plain,(
% 1.24/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1) | k4_orders_2(X0,X1) != X2 | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.24/1.01    inference(cnf_transformation,[],[f26])).
% 1.24/1.01  
% 1.24/1.01  fof(f49,plain,(
% 1.24/1.01    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_orders_2(X0,X1)) | ~m2_orders_2(X4,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.24/1.01    inference(equality_resolution,[],[f37])).
% 1.24/1.01  
% 1.24/1.01  fof(f48,plain,(
% 1.24/1.01    k1_xboole_0 = k3_tarski(k4_orders_2(sK2,sK3))),
% 1.24/1.01    inference(cnf_transformation,[],[f31])).
% 1.24/1.01  
% 1.24/1.01  fof(f4,axiom,(
% 1.24/1.01    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 1.24/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.24/1.01  
% 1.24/1.01  fof(f14,plain,(
% 1.24/1.01    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 1.24/1.01    inference(ennf_transformation,[],[f4])).
% 1.24/1.01  
% 1.24/1.01  fof(f35,plain,(
% 1.24/1.01    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 1.24/1.01    inference(cnf_transformation,[],[f14])).
% 1.24/1.01  
% 1.24/1.01  fof(f1,axiom,(
% 1.24/1.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.24/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.24/1.01  
% 1.24/1.01  fof(f10,plain,(
% 1.24/1.01    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 1.24/1.01    inference(unused_predicate_definition_removal,[],[f1])).
% 1.24/1.01  
% 1.24/1.01  fof(f11,plain,(
% 1.24/1.01    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 1.24/1.01    inference(ennf_transformation,[],[f10])).
% 1.24/1.01  
% 1.24/1.01  fof(f32,plain,(
% 1.24/1.01    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.24/1.01    inference(cnf_transformation,[],[f11])).
% 1.24/1.01  
% 1.24/1.01  fof(f2,axiom,(
% 1.24/1.01    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.24/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.24/1.01  
% 1.24/1.01  fof(f33,plain,(
% 1.24/1.01    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.24/1.01    inference(cnf_transformation,[],[f2])).
% 1.24/1.01  
% 1.24/1.01  fof(f3,axiom,(
% 1.24/1.01    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 1.24/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.24/1.01  
% 1.24/1.01  fof(f12,plain,(
% 1.24/1.01    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 1.24/1.01    inference(ennf_transformation,[],[f3])).
% 1.24/1.01  
% 1.24/1.01  fof(f13,plain,(
% 1.24/1.01    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 1.24/1.01    inference(flattening,[],[f12])).
% 1.24/1.01  
% 1.24/1.01  fof(f34,plain,(
% 1.24/1.01    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 1.24/1.01    inference(cnf_transformation,[],[f13])).
% 1.24/1.01  
% 1.24/1.01  cnf(c_9,plain,
% 1.24/1.01      ( ~ m2_orders_2(X0,X1,X2)
% 1.24/1.01      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.24/1.01      | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
% 1.24/1.01      | v2_struct_0(X1)
% 1.24/1.01      | ~ v3_orders_2(X1)
% 1.24/1.01      | ~ v4_orders_2(X1)
% 1.24/1.01      | ~ v5_orders_2(X1)
% 1.24/1.01      | ~ l1_orders_2(X1) ),
% 1.24/1.01      inference(cnf_transformation,[],[f41]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_11,negated_conjecture,
% 1.24/1.01      ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2))) ),
% 1.24/1.01      inference(cnf_transformation,[],[f47]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_327,plain,
% 1.24/1.01      ( ~ m2_orders_2(X0,X1,X2)
% 1.24/1.01      | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
% 1.24/1.01      | v2_struct_0(X1)
% 1.24/1.01      | ~ v3_orders_2(X1)
% 1.24/1.01      | ~ v4_orders_2(X1)
% 1.24/1.01      | ~ v5_orders_2(X1)
% 1.24/1.01      | ~ l1_orders_2(X1)
% 1.24/1.01      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK2))
% 1.24/1.01      | sK3 != X2 ),
% 1.24/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_11]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_328,plain,
% 1.24/1.01      ( ~ m2_orders_2(X0,X1,sK3)
% 1.24/1.01      | r2_hidden(k1_funct_1(sK3,u1_struct_0(X1)),X0)
% 1.24/1.01      | v2_struct_0(X1)
% 1.24/1.01      | ~ v3_orders_2(X1)
% 1.24/1.01      | ~ v4_orders_2(X1)
% 1.24/1.01      | ~ v5_orders_2(X1)
% 1.24/1.01      | ~ l1_orders_2(X1)
% 1.24/1.01      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK2)) ),
% 1.24/1.01      inference(unflattening,[status(thm)],[c_327]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_12,negated_conjecture,
% 1.24/1.01      ( l1_orders_2(sK2) ),
% 1.24/1.01      inference(cnf_transformation,[],[f46]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_514,plain,
% 1.24/1.01      ( ~ m2_orders_2(X0,X1,sK3)
% 1.24/1.01      | r2_hidden(k1_funct_1(sK3,u1_struct_0(X1)),X0)
% 1.24/1.01      | v2_struct_0(X1)
% 1.24/1.01      | ~ v3_orders_2(X1)
% 1.24/1.01      | ~ v4_orders_2(X1)
% 1.24/1.01      | ~ v5_orders_2(X1)
% 1.24/1.01      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK2))
% 1.24/1.01      | sK2 != X1 ),
% 1.24/1.01      inference(resolution_lifted,[status(thm)],[c_328,c_12]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_515,plain,
% 1.24/1.01      ( ~ m2_orders_2(X0,sK2,sK3)
% 1.24/1.01      | r2_hidden(k1_funct_1(sK3,u1_struct_0(sK2)),X0)
% 1.24/1.01      | v2_struct_0(sK2)
% 1.24/1.01      | ~ v3_orders_2(sK2)
% 1.24/1.01      | ~ v4_orders_2(sK2)
% 1.24/1.01      | ~ v5_orders_2(sK2)
% 1.24/1.01      | k1_orders_1(u1_struct_0(sK2)) != k1_orders_1(u1_struct_0(sK2)) ),
% 1.24/1.01      inference(unflattening,[status(thm)],[c_514]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_16,negated_conjecture,
% 1.24/1.01      ( ~ v2_struct_0(sK2) ),
% 1.24/1.01      inference(cnf_transformation,[],[f42]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_15,negated_conjecture,
% 1.24/1.01      ( v3_orders_2(sK2) ),
% 1.24/1.01      inference(cnf_transformation,[],[f43]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_14,negated_conjecture,
% 1.24/1.01      ( v4_orders_2(sK2) ),
% 1.24/1.01      inference(cnf_transformation,[],[f44]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_13,negated_conjecture,
% 1.24/1.01      ( v5_orders_2(sK2) ),
% 1.24/1.01      inference(cnf_transformation,[],[f45]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_519,plain,
% 1.24/1.01      ( ~ m2_orders_2(X0,sK2,sK3)
% 1.24/1.01      | r2_hidden(k1_funct_1(sK3,u1_struct_0(sK2)),X0)
% 1.24/1.01      | k1_orders_1(u1_struct_0(sK2)) != k1_orders_1(u1_struct_0(sK2)) ),
% 1.24/1.01      inference(global_propositional_subsumption,
% 1.24/1.01                [status(thm)],
% 1.24/1.01                [c_515,c_16,c_15,c_14,c_13]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_757,plain,
% 1.24/1.01      ( ~ m2_orders_2(X0,sK2,sK3)
% 1.24/1.01      | r2_hidden(k1_funct_1(sK3,u1_struct_0(sK2)),X0) ),
% 1.24/1.01      inference(equality_resolution_simp,[status(thm)],[c_519]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_1171,plain,
% 1.24/1.01      ( m2_orders_2(X0,sK2,sK3) != iProver_top
% 1.24/1.01      | r2_hidden(k1_funct_1(sK3,u1_struct_0(sK2)),X0) = iProver_top ),
% 1.24/1.01      inference(predicate_to_equality,[status(thm)],[c_757]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_8,plain,
% 1.24/1.01      ( m2_orders_2(sK1(X0,X1),X0,X1)
% 1.24/1.01      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
% 1.24/1.01      | v2_struct_0(X0)
% 1.24/1.01      | ~ v3_orders_2(X0)
% 1.24/1.01      | ~ v4_orders_2(X0)
% 1.24/1.01      | ~ v5_orders_2(X0)
% 1.24/1.01      | ~ l1_orders_2(X0) ),
% 1.24/1.01      inference(cnf_transformation,[],[f40]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_234,plain,
% 1.24/1.01      ( m2_orders_2(sK1(X0,X1),X0,X1)
% 1.24/1.01      | v2_struct_0(X0)
% 1.24/1.01      | ~ v3_orders_2(X0)
% 1.24/1.01      | ~ v4_orders_2(X0)
% 1.24/1.01      | ~ v5_orders_2(X0)
% 1.24/1.01      | ~ l1_orders_2(X0)
% 1.24/1.01      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK2))
% 1.24/1.01      | sK3 != X1 ),
% 1.24/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_11]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_235,plain,
% 1.24/1.01      ( m2_orders_2(sK1(X0,sK3),X0,sK3)
% 1.24/1.01      | v2_struct_0(X0)
% 1.24/1.01      | ~ v3_orders_2(X0)
% 1.24/1.01      | ~ v4_orders_2(X0)
% 1.24/1.01      | ~ v5_orders_2(X0)
% 1.24/1.01      | ~ l1_orders_2(X0)
% 1.24/1.01      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK2)) ),
% 1.24/1.01      inference(unflattening,[status(thm)],[c_234]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_583,plain,
% 1.24/1.01      ( m2_orders_2(sK1(X0,sK3),X0,sK3)
% 1.24/1.01      | v2_struct_0(X0)
% 1.24/1.01      | ~ v3_orders_2(X0)
% 1.24/1.01      | ~ v4_orders_2(X0)
% 1.24/1.01      | ~ v5_orders_2(X0)
% 1.24/1.01      | k1_orders_1(u1_struct_0(X0)) != k1_orders_1(u1_struct_0(sK2))
% 1.24/1.01      | sK2 != X0 ),
% 1.24/1.01      inference(resolution_lifted,[status(thm)],[c_235,c_12]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_584,plain,
% 1.24/1.01      ( m2_orders_2(sK1(sK2,sK3),sK2,sK3)
% 1.24/1.01      | v2_struct_0(sK2)
% 1.24/1.01      | ~ v3_orders_2(sK2)
% 1.24/1.01      | ~ v4_orders_2(sK2)
% 1.24/1.01      | ~ v5_orders_2(sK2)
% 1.24/1.01      | k1_orders_1(u1_struct_0(sK2)) != k1_orders_1(u1_struct_0(sK2)) ),
% 1.24/1.01      inference(unflattening,[status(thm)],[c_583]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_586,plain,
% 1.24/1.01      ( m2_orders_2(sK1(sK2,sK3),sK2,sK3)
% 1.24/1.01      | k1_orders_1(u1_struct_0(sK2)) != k1_orders_1(u1_struct_0(sK2)) ),
% 1.24/1.01      inference(global_propositional_subsumption,
% 1.24/1.01                [status(thm)],
% 1.24/1.01                [c_584,c_16,c_15,c_14,c_13]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_747,plain,
% 1.24/1.01      ( m2_orders_2(sK1(sK2,sK3),sK2,sK3) ),
% 1.24/1.01      inference(equality_resolution_simp,[status(thm)],[c_586]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_1174,plain,
% 1.24/1.01      ( m2_orders_2(sK1(sK2,sK3),sK2,sK3) = iProver_top ),
% 1.24/1.01      inference(predicate_to_equality,[status(thm)],[c_747]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_6,plain,
% 1.24/1.01      ( ~ m2_orders_2(X0,X1,X2)
% 1.24/1.01      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.24/1.01      | r2_hidden(X0,k4_orders_2(X1,X2))
% 1.24/1.01      | v2_struct_0(X1)
% 1.24/1.01      | ~ v3_orders_2(X1)
% 1.24/1.01      | ~ v4_orders_2(X1)
% 1.24/1.01      | ~ v5_orders_2(X1)
% 1.24/1.01      | ~ l1_orders_2(X1) ),
% 1.24/1.01      inference(cnf_transformation,[],[f49]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_387,plain,
% 1.24/1.01      ( ~ m2_orders_2(X0,X1,X2)
% 1.24/1.01      | r2_hidden(X0,k4_orders_2(X1,X2))
% 1.24/1.01      | v2_struct_0(X1)
% 1.24/1.01      | ~ v3_orders_2(X1)
% 1.24/1.01      | ~ v4_orders_2(X1)
% 1.24/1.01      | ~ v5_orders_2(X1)
% 1.24/1.01      | ~ l1_orders_2(X1)
% 1.24/1.01      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK2))
% 1.24/1.01      | sK3 != X2 ),
% 1.24/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_11]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_388,plain,
% 1.24/1.01      ( ~ m2_orders_2(X0,X1,sK3)
% 1.24/1.01      | r2_hidden(X0,k4_orders_2(X1,sK3))
% 1.24/1.01      | v2_struct_0(X1)
% 1.24/1.01      | ~ v3_orders_2(X1)
% 1.24/1.01      | ~ v4_orders_2(X1)
% 1.24/1.01      | ~ v5_orders_2(X1)
% 1.24/1.01      | ~ l1_orders_2(X1)
% 1.24/1.01      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK2)) ),
% 1.24/1.01      inference(unflattening,[status(thm)],[c_387]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_472,plain,
% 1.24/1.01      ( ~ m2_orders_2(X0,X1,sK3)
% 1.24/1.01      | r2_hidden(X0,k4_orders_2(X1,sK3))
% 1.24/1.01      | v2_struct_0(X1)
% 1.24/1.01      | ~ v3_orders_2(X1)
% 1.24/1.01      | ~ v4_orders_2(X1)
% 1.24/1.01      | ~ v5_orders_2(X1)
% 1.24/1.01      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK2))
% 1.24/1.01      | sK2 != X1 ),
% 1.24/1.01      inference(resolution_lifted,[status(thm)],[c_388,c_12]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_473,plain,
% 1.24/1.01      ( ~ m2_orders_2(X0,sK2,sK3)
% 1.24/1.01      | r2_hidden(X0,k4_orders_2(sK2,sK3))
% 1.24/1.01      | v2_struct_0(sK2)
% 1.24/1.01      | ~ v3_orders_2(sK2)
% 1.24/1.01      | ~ v4_orders_2(sK2)
% 1.24/1.01      | ~ v5_orders_2(sK2)
% 1.24/1.01      | k1_orders_1(u1_struct_0(sK2)) != k1_orders_1(u1_struct_0(sK2)) ),
% 1.24/1.01      inference(unflattening,[status(thm)],[c_472]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_477,plain,
% 1.24/1.01      ( ~ m2_orders_2(X0,sK2,sK3)
% 1.24/1.01      | r2_hidden(X0,k4_orders_2(sK2,sK3))
% 1.24/1.01      | k1_orders_1(u1_struct_0(sK2)) != k1_orders_1(u1_struct_0(sK2)) ),
% 1.24/1.01      inference(global_propositional_subsumption,
% 1.24/1.01                [status(thm)],
% 1.24/1.01                [c_473,c_16,c_15,c_14,c_13]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_765,plain,
% 1.24/1.01      ( ~ m2_orders_2(X0,sK2,sK3) | r2_hidden(X0,k4_orders_2(sK2,sK3)) ),
% 1.24/1.01      inference(equality_resolution_simp,[status(thm)],[c_477]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_782,plain,
% 1.24/1.01      ( ~ m2_orders_2(X0,sK2,sK3) | r2_hidden(X0,k4_orders_2(sK2,sK3)) ),
% 1.24/1.01      inference(prop_impl,[status(thm)],[c_765]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_1169,plain,
% 1.24/1.01      ( m2_orders_2(X0,sK2,sK3) != iProver_top
% 1.24/1.01      | r2_hidden(X0,k4_orders_2(sK2,sK3)) = iProver_top ),
% 1.24/1.01      inference(predicate_to_equality,[status(thm)],[c_782]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_10,negated_conjecture,
% 1.24/1.01      ( k1_xboole_0 = k3_tarski(k4_orders_2(sK2,sK3)) ),
% 1.24/1.01      inference(cnf_transformation,[],[f48]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_3,plain,
% 1.24/1.01      ( r1_tarski(X0,k3_tarski(X1)) | ~ r2_hidden(X0,X1) ),
% 1.24/1.01      inference(cnf_transformation,[],[f35]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_0,plain,
% 1.24/1.01      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 1.24/1.01      inference(cnf_transformation,[],[f32]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_1,plain,
% 1.24/1.01      ( r1_xboole_0(X0,k1_xboole_0) ),
% 1.24/1.01      inference(cnf_transformation,[],[f33]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_2,plain,
% 1.24/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X0,X1) | v1_xboole_0(X0) ),
% 1.24/1.01      inference(cnf_transformation,[],[f34]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_185,plain,
% 1.24/1.01      ( ~ r1_tarski(X0,X1)
% 1.24/1.01      | v1_xboole_0(X0)
% 1.24/1.01      | X0 != X2
% 1.24/1.01      | k1_xboole_0 != X1 ),
% 1.24/1.01      inference(resolution_lifted,[status(thm)],[c_1,c_2]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_186,plain,
% 1.24/1.01      ( ~ r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0) ),
% 1.24/1.01      inference(unflattening,[status(thm)],[c_185]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_200,plain,
% 1.24/1.01      ( ~ r1_tarski(X0,k1_xboole_0) | ~ r2_hidden(X1,X2) | X0 != X2 ),
% 1.24/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_186]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_201,plain,
% 1.24/1.01      ( ~ r1_tarski(X0,k1_xboole_0) | ~ r2_hidden(X1,X0) ),
% 1.24/1.01      inference(unflattening,[status(thm)],[c_200]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_215,plain,
% 1.24/1.01      ( ~ r2_hidden(X0,X1)
% 1.24/1.01      | ~ r2_hidden(X2,X3)
% 1.24/1.01      | X3 != X0
% 1.24/1.01      | k3_tarski(X1) != k1_xboole_0 ),
% 1.24/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_201]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_216,plain,
% 1.24/1.01      ( ~ r2_hidden(X0,X1)
% 1.24/1.01      | ~ r2_hidden(X2,X0)
% 1.24/1.01      | k3_tarski(X1) != k1_xboole_0 ),
% 1.24/1.01      inference(unflattening,[status(thm)],[c_215]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_1175,plain,
% 1.24/1.01      ( k3_tarski(X0) != k1_xboole_0
% 1.24/1.01      | r2_hidden(X1,X0) != iProver_top
% 1.24/1.01      | r2_hidden(X2,X1) != iProver_top ),
% 1.24/1.01      inference(predicate_to_equality,[status(thm)],[c_216]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_1414,plain,
% 1.24/1.01      ( r2_hidden(X0,X1) != iProver_top
% 1.24/1.01      | r2_hidden(X1,k4_orders_2(sK2,sK3)) != iProver_top ),
% 1.24/1.01      inference(superposition,[status(thm)],[c_10,c_1175]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_1471,plain,
% 1.24/1.01      ( m2_orders_2(X0,sK2,sK3) != iProver_top
% 1.24/1.01      | r2_hidden(X1,X0) != iProver_top ),
% 1.24/1.01      inference(superposition,[status(thm)],[c_1169,c_1414]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_1491,plain,
% 1.24/1.01      ( r2_hidden(X0,sK1(sK2,sK3)) != iProver_top ),
% 1.24/1.01      inference(superposition,[status(thm)],[c_1174,c_1471]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_1626,plain,
% 1.24/1.01      ( m2_orders_2(sK1(sK2,sK3),sK2,sK3) != iProver_top ),
% 1.24/1.01      inference(superposition,[status(thm)],[c_1171,c_1491]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(c_748,plain,
% 1.24/1.01      ( m2_orders_2(sK1(sK2,sK3),sK2,sK3) = iProver_top ),
% 1.24/1.01      inference(predicate_to_equality,[status(thm)],[c_747]) ).
% 1.24/1.01  
% 1.24/1.01  cnf(contradiction,plain,
% 1.24/1.01      ( $false ),
% 1.24/1.01      inference(minisat,[status(thm)],[c_1626,c_748]) ).
% 1.24/1.01  
% 1.24/1.01  
% 1.24/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 1.24/1.01  
% 1.24/1.01  ------                               Statistics
% 1.24/1.01  
% 1.24/1.01  ------ General
% 1.24/1.01  
% 1.24/1.01  abstr_ref_over_cycles:                  0
% 1.24/1.01  abstr_ref_under_cycles:                 0
% 1.24/1.01  gc_basic_clause_elim:                   0
% 1.24/1.01  forced_gc_time:                         0
% 1.24/1.01  parsing_time:                           0.01
% 1.24/1.01  unif_index_cands_time:                  0.
% 1.24/1.01  unif_index_add_time:                    0.
% 1.24/1.01  orderings_time:                         0.
% 1.24/1.01  out_proof_time:                         0.009
% 1.24/1.01  total_time:                             0.081
% 1.24/1.01  num_of_symbols:                         52
% 1.24/1.01  num_of_terms:                           953
% 1.24/1.01  
% 1.24/1.01  ------ Preprocessing
% 1.24/1.01  
% 1.24/1.01  num_of_splits:                          0
% 1.24/1.01  num_of_split_atoms:                     0
% 1.24/1.01  num_of_reused_defs:                     0
% 1.24/1.01  num_eq_ax_congr_red:                    13
% 1.24/1.01  num_of_sem_filtered_clauses:            1
% 1.24/1.01  num_of_subtypes:                        0
% 1.24/1.01  monotx_restored_types:                  0
% 1.24/1.01  sat_num_of_epr_types:                   0
% 1.24/1.01  sat_num_of_non_cyclic_types:            0
% 1.24/1.01  sat_guarded_non_collapsed_types:        0
% 1.24/1.01  num_pure_diseq_elim:                    0
% 1.24/1.01  simp_replaced_by:                       0
% 1.24/1.01  res_preprocessed:                       62
% 1.24/1.01  prep_upred:                             0
% 1.24/1.01  prep_unflattend:                        26
% 1.24/1.01  smt_new_axioms:                         0
% 1.24/1.01  pred_elim_cands:                        2
% 1.24/1.01  pred_elim:                              9
% 1.24/1.01  pred_elim_cl:                           9
% 1.24/1.01  pred_elim_cycles:                       11
% 1.24/1.01  merged_defs:                            6
% 1.24/1.01  merged_defs_ncl:                        0
% 1.24/1.01  bin_hyper_res:                          6
% 1.24/1.01  prep_cycles:                            4
% 1.24/1.01  pred_elim_time:                         0.013
% 1.24/1.01  splitting_time:                         0.
% 1.24/1.01  sem_filter_time:                        0.
% 1.24/1.01  monotx_time:                            0.001
% 1.24/1.01  subtype_inf_time:                       0.
% 1.24/1.01  
% 1.24/1.01  ------ Problem properties
% 1.24/1.01  
% 1.24/1.01  clauses:                                8
% 1.24/1.01  conjectures:                            1
% 1.24/1.01  epr:                                    0
% 1.24/1.01  horn:                                   7
% 1.24/1.01  ground:                                 2
% 1.24/1.01  unary:                                  2
% 1.24/1.01  binary:                                 3
% 1.24/1.01  lits:                                   17
% 1.24/1.01  lits_eq:                                4
% 1.24/1.01  fd_pure:                                0
% 1.24/1.01  fd_pseudo:                              0
% 1.24/1.01  fd_cond:                                2
% 1.24/1.01  fd_pseudo_cond:                         0
% 1.24/1.01  ac_symbols:                             0
% 1.24/1.01  
% 1.24/1.01  ------ Propositional Solver
% 1.24/1.01  
% 1.24/1.01  prop_solver_calls:                      27
% 1.24/1.01  prop_fast_solver_calls:                 530
% 1.24/1.01  smt_solver_calls:                       0
% 1.24/1.01  smt_fast_solver_calls:                  0
% 1.24/1.01  prop_num_of_clauses:                    404
% 1.24/1.01  prop_preprocess_simplified:             1849
% 1.24/1.01  prop_fo_subsumed:                       24
% 1.24/1.01  prop_solver_time:                       0.
% 1.24/1.01  smt_solver_time:                        0.
% 1.24/1.01  smt_fast_solver_time:                   0.
% 1.24/1.01  prop_fast_solver_time:                  0.
% 1.24/1.01  prop_unsat_core_time:                   0.
% 1.24/1.01  
% 1.24/1.01  ------ QBF
% 1.24/1.01  
% 1.24/1.01  qbf_q_res:                              0
% 1.24/1.01  qbf_num_tautologies:                    0
% 1.24/1.01  qbf_prep_cycles:                        0
% 1.24/1.01  
% 1.24/1.01  ------ BMC1
% 1.24/1.01  
% 1.24/1.01  bmc1_current_bound:                     -1
% 1.24/1.01  bmc1_last_solved_bound:                 -1
% 1.24/1.01  bmc1_unsat_core_size:                   -1
% 1.24/1.01  bmc1_unsat_core_parents_size:           -1
% 1.24/1.01  bmc1_merge_next_fun:                    0
% 1.24/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.24/1.01  
% 1.24/1.01  ------ Instantiation
% 1.24/1.01  
% 1.24/1.01  inst_num_of_clauses:                    95
% 1.24/1.01  inst_num_in_passive:                    26
% 1.24/1.01  inst_num_in_active:                     54
% 1.24/1.01  inst_num_in_unprocessed:                15
% 1.24/1.01  inst_num_of_loops:                      70
% 1.24/1.01  inst_num_of_learning_restarts:          0
% 1.24/1.01  inst_num_moves_active_passive:          13
% 1.24/1.01  inst_lit_activity:                      0
% 1.24/1.01  inst_lit_activity_moves:                0
% 1.24/1.01  inst_num_tautologies:                   0
% 1.24/1.01  inst_num_prop_implied:                  0
% 1.24/1.01  inst_num_existing_simplified:           0
% 1.24/1.01  inst_num_eq_res_simplified:             0
% 1.24/1.01  inst_num_child_elim:                    0
% 1.24/1.01  inst_num_of_dismatching_blockings:      2
% 1.24/1.01  inst_num_of_non_proper_insts:           71
% 1.24/1.01  inst_num_of_duplicates:                 0
% 1.24/1.01  inst_inst_num_from_inst_to_res:         0
% 1.24/1.01  inst_dismatching_checking_time:         0.
% 1.24/1.01  
% 1.24/1.01  ------ Resolution
% 1.24/1.01  
% 1.24/1.01  res_num_of_clauses:                     0
% 1.24/1.01  res_num_in_passive:                     0
% 1.24/1.01  res_num_in_active:                      0
% 1.24/1.01  res_num_of_loops:                       66
% 1.24/1.01  res_forward_subset_subsumed:            13
% 1.24/1.01  res_backward_subset_subsumed:           0
% 1.24/1.01  res_forward_subsumed:                   0
% 1.24/1.01  res_backward_subsumed:                  0
% 1.24/1.01  res_forward_subsumption_resolution:     0
% 1.24/1.01  res_backward_subsumption_resolution:    0
% 1.24/1.01  res_clause_to_clause_subsumption:       24
% 1.24/1.01  res_orphan_elimination:                 0
% 1.24/1.01  res_tautology_del:                      27
% 1.24/1.01  res_num_eq_res_simplified:              6
% 1.24/1.01  res_num_sel_changes:                    0
% 1.24/1.01  res_moves_from_active_to_pass:          0
% 1.24/1.01  
% 1.24/1.01  ------ Superposition
% 1.24/1.01  
% 1.24/1.01  sup_time_total:                         0.
% 1.24/1.01  sup_time_generating:                    0.
% 1.24/1.01  sup_time_sim_full:                      0.
% 1.24/1.01  sup_time_sim_immed:                     0.
% 1.24/1.01  
% 1.24/1.01  sup_num_of_clauses:                     16
% 1.24/1.01  sup_num_in_active:                      13
% 1.24/1.01  sup_num_in_passive:                     3
% 1.24/1.01  sup_num_of_loops:                       12
% 1.24/1.01  sup_fw_superposition:                   11
% 1.24/1.01  sup_bw_superposition:                   2
% 1.24/1.01  sup_immediate_simplified:               0
% 1.24/1.01  sup_given_eliminated:                   0
% 1.24/1.01  comparisons_done:                       0
% 1.24/1.01  comparisons_avoided:                    0
% 1.24/1.01  
% 1.24/1.01  ------ Simplifications
% 1.24/1.01  
% 1.24/1.01  
% 1.24/1.01  sim_fw_subset_subsumed:                 0
% 1.24/1.01  sim_bw_subset_subsumed:                 0
% 1.24/1.01  sim_fw_subsumed:                        0
% 1.24/1.01  sim_bw_subsumed:                        0
% 1.24/1.01  sim_fw_subsumption_res:                 0
% 1.24/1.01  sim_bw_subsumption_res:                 0
% 1.24/1.01  sim_tautology_del:                      2
% 1.24/1.01  sim_eq_tautology_del:                   2
% 1.24/1.01  sim_eq_res_simp:                        0
% 1.24/1.01  sim_fw_demodulated:                     0
% 1.24/1.01  sim_bw_demodulated:                     0
% 1.24/1.01  sim_light_normalised:                   0
% 1.24/1.01  sim_joinable_taut:                      0
% 1.24/1.01  sim_joinable_simp:                      0
% 1.24/1.01  sim_ac_normalised:                      0
% 1.24/1.01  sim_smt_subsumption:                    0
% 1.24/1.01  
%------------------------------------------------------------------------------
