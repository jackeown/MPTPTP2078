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
% DateTime   : Thu Dec  3 11:32:38 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :  111 (1839 expanded)
%              Number of clauses        :   47 ( 267 expanded)
%              Number of leaves         :   16 ( 533 expanded)
%              Depth                    :   23
%              Number of atoms          :  328 (4677 expanded)
%              Number of equality atoms :  193 (3312 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f23])).

fof(f41,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f70,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f41,f34])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( k1_xboole_0 != sK5
      & k1_xboole_0 != sK4
      & sK4 != sK5
      & k2_xboole_0(sK4,sK5) = k1_tarski(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( k1_xboole_0 != sK5
    & k1_xboole_0 != sK4
    & sK4 != sK5
    & k2_xboole_0(sK4,sK5) = k1_tarski(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f17,f32])).

fof(f57,plain,(
    k2_xboole_0(sK4,sK5) = k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f56,f61])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f48,f61])).

fof(f84,plain,(
    k2_enumset1(sK3,sK3,sK3,sK3) = k3_tarski(k2_enumset1(sK4,sK4,sK4,sK5)) ),
    inference(definition_unfolding,[],[f57,f62,f63])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f72,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f43,f62])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f30])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) = X0
      | o_0_0_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f53,f63,f34,f63])).

fof(f59,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f33])).

fof(f83,plain,(
    o_0_0_xboole_0 != sK4 ),
    inference(definition_unfolding,[],[f59,f34])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f44,f63])).

fof(f90,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f76])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f45,f63])).

fof(f88,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f75])).

fof(f89,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f88])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f18])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & ~ r2_hidden(sK0(X0,X1,X2),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(sK0(X0,X1,X2),X1)
          | r2_hidden(sK0(X0,X1,X2),X0)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & ~ r2_hidden(sK0(X0,X1,X2),X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( r2_hidden(sK0(X0,X1,X2),X1)
            | r2_hidden(sK0(X0,X1,X2),X0)
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k2_enumset1(X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f37,f62])).

fof(f85,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k2_enumset1(X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f67])).

fof(f60,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f33])).

fof(f82,plain,(
    o_0_0_xboole_0 != sK5 ),
    inference(definition_unfolding,[],[f60,f34])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f38,f62])).

fof(f58,plain,(
    sK4 != sK5 ),
    inference(cnf_transformation,[],[f33])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f40,f62])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0),X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_788,plain,
    ( o_0_0_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_21,negated_conjecture,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k3_tarski(k2_enumset1(sK4,sK4,sK4,sK5)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_8,plain,
    ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_786,plain,
    ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1066,plain,
    ( r1_tarski(sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_786])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
    | k2_enumset1(X1,X1,X1,X1) = X0
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_777,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | o_0_0_xboole_0 = X1
    | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1272,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = sK4
    | sK4 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_1066,c_777])).

cnf(c_19,negated_conjecture,
    ( o_0_0_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_38,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,k2_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))
    | o_0_0_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_11,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_41,plain,
    ( r2_hidden(o_0_0_xboole_0,k2_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_363,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_931,plain,
    ( sK4 != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_363])).

cnf(c_932,plain,
    ( sK4 != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK4
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_931])).

cnf(c_1627,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1272,c_19,c_38,c_41,c_932])).

cnf(c_1632,plain,
    ( k3_tarski(k2_enumset1(sK4,sK4,sK4,sK5)) = sK4 ),
    inference(demodulation,[status(thm)],[c_1627,c_21])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_791,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2069,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1632,c_791])).

cnf(c_2234,plain,
    ( sK5 = o_0_0_xboole_0
    | r2_hidden(sK1(sK5),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_788,c_2069])).

cnf(c_18,negated_conjecture,
    ( o_0_0_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_929,plain,
    ( sK5 != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_363])).

cnf(c_930,plain,
    ( sK5 != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK5
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_929])).

cnf(c_2553,plain,
    ( r2_hidden(sK1(sK5),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2234,c_18,c_38,c_41,c_930])).

cnf(c_782,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1646,plain,
    ( sK3 = X0
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1627,c_782])).

cnf(c_2558,plain,
    ( sK1(sK5) = sK3 ),
    inference(superposition,[status(thm)],[c_2553,c_1646])).

cnf(c_7041,plain,
    ( sK5 = o_0_0_xboole_0
    | r2_hidden(sK3,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2558,c_788])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X0)
    | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_792,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3172,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = sK5
    | r2_hidden(sK0(X0,X1,sK5),X1) = iProver_top
    | r2_hidden(sK0(X0,X1,sK5),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,sK5),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_792,c_2069])).

cnf(c_4162,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,sK5)) = sK5
    | r2_hidden(sK0(X0,sK5,sK5),X0) = iProver_top
    | r2_hidden(sK0(X0,sK5,sK5),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3172,c_2069])).

cnf(c_4308,plain,
    ( k3_tarski(k2_enumset1(sK4,sK4,sK4,sK5)) = sK5
    | r2_hidden(sK0(sK4,sK5,sK5),sK4) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_4162])).

cnf(c_4310,plain,
    ( k3_tarski(k2_enumset1(sK4,sK4,sK4,sK5)) = sK5
    | r2_hidden(sK0(sK4,sK5,sK5),sK4) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4308])).

cnf(c_4313,plain,
    ( sK4 = sK5
    | r2_hidden(sK0(sK4,sK5,sK5),sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4310,c_1632])).

cnf(c_20,negated_conjecture,
    ( sK4 != sK5 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_4546,plain,
    ( r2_hidden(sK0(sK4,sK5,sK5),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4313,c_20])).

cnf(c_4551,plain,
    ( sK0(sK4,sK5,sK5) = sK3 ),
    inference(superposition,[status(thm)],[c_4546,c_1646])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_794,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4867,plain,
    ( k3_tarski(k2_enumset1(sK4,sK4,sK4,sK5)) = sK5
    | r2_hidden(sK0(sK4,sK5,sK5),sK5) != iProver_top
    | r2_hidden(sK3,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4551,c_794])).

cnf(c_4890,plain,
    ( k3_tarski(k2_enumset1(sK4,sK4,sK4,sK5)) = sK5
    | r2_hidden(sK3,sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4867,c_4551])).

cnf(c_4891,plain,
    ( sK4 = sK5
    | r2_hidden(sK3,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4890,c_1632])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7041,c_4891,c_930,c_41,c_38,c_18,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:38:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.00/1.04  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.04  
% 3.00/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.00/1.04  
% 3.00/1.04  ------  iProver source info
% 3.00/1.04  
% 3.00/1.04  git: date: 2020-06-30 10:37:57 +0100
% 3.00/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.00/1.04  git: non_committed_changes: false
% 3.00/1.04  git: last_make_outside_of_git: false
% 3.00/1.04  
% 3.00/1.04  ------ 
% 3.00/1.04  
% 3.00/1.04  ------ Input Options
% 3.00/1.04  
% 3.00/1.04  --out_options                           all
% 3.00/1.04  --tptp_safe_out                         true
% 3.00/1.04  --problem_path                          ""
% 3.00/1.04  --include_path                          ""
% 3.00/1.04  --clausifier                            res/vclausify_rel
% 3.00/1.04  --clausifier_options                    --mode clausify
% 3.00/1.04  --stdin                                 false
% 3.00/1.04  --stats_out                             all
% 3.00/1.04  
% 3.00/1.04  ------ General Options
% 3.00/1.04  
% 3.00/1.04  --fof                                   false
% 3.00/1.04  --time_out_real                         305.
% 3.00/1.04  --time_out_virtual                      -1.
% 3.00/1.04  --symbol_type_check                     false
% 3.00/1.04  --clausify_out                          false
% 3.00/1.04  --sig_cnt_out                           false
% 3.00/1.04  --trig_cnt_out                          false
% 3.00/1.04  --trig_cnt_out_tolerance                1.
% 3.00/1.04  --trig_cnt_out_sk_spl                   false
% 3.00/1.04  --abstr_cl_out                          false
% 3.00/1.04  
% 3.00/1.04  ------ Global Options
% 3.00/1.04  
% 3.00/1.04  --schedule                              default
% 3.00/1.04  --add_important_lit                     false
% 3.00/1.04  --prop_solver_per_cl                    1000
% 3.00/1.04  --min_unsat_core                        false
% 3.00/1.04  --soft_assumptions                      false
% 3.00/1.04  --soft_lemma_size                       3
% 3.00/1.04  --prop_impl_unit_size                   0
% 3.00/1.04  --prop_impl_unit                        []
% 3.00/1.04  --share_sel_clauses                     true
% 3.00/1.04  --reset_solvers                         false
% 3.00/1.04  --bc_imp_inh                            [conj_cone]
% 3.00/1.04  --conj_cone_tolerance                   3.
% 3.00/1.04  --extra_neg_conj                        none
% 3.00/1.04  --large_theory_mode                     true
% 3.00/1.04  --prolific_symb_bound                   200
% 3.00/1.04  --lt_threshold                          2000
% 3.00/1.04  --clause_weak_htbl                      true
% 3.00/1.04  --gc_record_bc_elim                     false
% 3.00/1.04  
% 3.00/1.04  ------ Preprocessing Options
% 3.00/1.04  
% 3.00/1.04  --preprocessing_flag                    true
% 3.00/1.04  --time_out_prep_mult                    0.1
% 3.00/1.04  --splitting_mode                        input
% 3.00/1.04  --splitting_grd                         true
% 3.00/1.04  --splitting_cvd                         false
% 3.00/1.04  --splitting_cvd_svl                     false
% 3.00/1.04  --splitting_nvd                         32
% 3.00/1.04  --sub_typing                            true
% 3.00/1.04  --prep_gs_sim                           true
% 3.00/1.04  --prep_unflatten                        true
% 3.00/1.04  --prep_res_sim                          true
% 3.00/1.04  --prep_upred                            true
% 3.00/1.04  --prep_sem_filter                       exhaustive
% 3.00/1.04  --prep_sem_filter_out                   false
% 3.00/1.04  --pred_elim                             true
% 3.00/1.04  --res_sim_input                         true
% 3.00/1.04  --eq_ax_congr_red                       true
% 3.00/1.04  --pure_diseq_elim                       true
% 3.00/1.04  --brand_transform                       false
% 3.00/1.04  --non_eq_to_eq                          false
% 3.00/1.04  --prep_def_merge                        true
% 3.00/1.04  --prep_def_merge_prop_impl              false
% 3.00/1.04  --prep_def_merge_mbd                    true
% 3.00/1.04  --prep_def_merge_tr_red                 false
% 3.00/1.04  --prep_def_merge_tr_cl                  false
% 3.00/1.04  --smt_preprocessing                     true
% 3.00/1.04  --smt_ac_axioms                         fast
% 3.00/1.04  --preprocessed_out                      false
% 3.00/1.04  --preprocessed_stats                    false
% 3.00/1.04  
% 3.00/1.04  ------ Abstraction refinement Options
% 3.00/1.04  
% 3.00/1.04  --abstr_ref                             []
% 3.00/1.04  --abstr_ref_prep                        false
% 3.00/1.04  --abstr_ref_until_sat                   false
% 3.00/1.04  --abstr_ref_sig_restrict                funpre
% 3.00/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/1.04  --abstr_ref_under                       []
% 3.00/1.04  
% 3.00/1.04  ------ SAT Options
% 3.00/1.04  
% 3.00/1.04  --sat_mode                              false
% 3.00/1.04  --sat_fm_restart_options                ""
% 3.00/1.04  --sat_gr_def                            false
% 3.00/1.04  --sat_epr_types                         true
% 3.00/1.04  --sat_non_cyclic_types                  false
% 3.00/1.04  --sat_finite_models                     false
% 3.00/1.04  --sat_fm_lemmas                         false
% 3.00/1.04  --sat_fm_prep                           false
% 3.00/1.04  --sat_fm_uc_incr                        true
% 3.00/1.04  --sat_out_model                         small
% 3.00/1.04  --sat_out_clauses                       false
% 3.00/1.04  
% 3.00/1.04  ------ QBF Options
% 3.00/1.04  
% 3.00/1.04  --qbf_mode                              false
% 3.00/1.04  --qbf_elim_univ                         false
% 3.00/1.04  --qbf_dom_inst                          none
% 3.00/1.04  --qbf_dom_pre_inst                      false
% 3.00/1.04  --qbf_sk_in                             false
% 3.00/1.04  --qbf_pred_elim                         true
% 3.00/1.04  --qbf_split                             512
% 3.00/1.04  
% 3.00/1.04  ------ BMC1 Options
% 3.00/1.04  
% 3.00/1.04  --bmc1_incremental                      false
% 3.00/1.04  --bmc1_axioms                           reachable_all
% 3.00/1.04  --bmc1_min_bound                        0
% 3.00/1.04  --bmc1_max_bound                        -1
% 3.00/1.04  --bmc1_max_bound_default                -1
% 3.00/1.04  --bmc1_symbol_reachability              true
% 3.00/1.04  --bmc1_property_lemmas                  false
% 3.00/1.04  --bmc1_k_induction                      false
% 3.00/1.04  --bmc1_non_equiv_states                 false
% 3.00/1.04  --bmc1_deadlock                         false
% 3.00/1.04  --bmc1_ucm                              false
% 3.00/1.04  --bmc1_add_unsat_core                   none
% 3.00/1.04  --bmc1_unsat_core_children              false
% 3.00/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/1.04  --bmc1_out_stat                         full
% 3.00/1.04  --bmc1_ground_init                      false
% 3.00/1.04  --bmc1_pre_inst_next_state              false
% 3.00/1.04  --bmc1_pre_inst_state                   false
% 3.00/1.04  --bmc1_pre_inst_reach_state             false
% 3.00/1.04  --bmc1_out_unsat_core                   false
% 3.00/1.04  --bmc1_aig_witness_out                  false
% 3.00/1.04  --bmc1_verbose                          false
% 3.00/1.04  --bmc1_dump_clauses_tptp                false
% 3.00/1.04  --bmc1_dump_unsat_core_tptp             false
% 3.00/1.04  --bmc1_dump_file                        -
% 3.00/1.04  --bmc1_ucm_expand_uc_limit              128
% 3.00/1.04  --bmc1_ucm_n_expand_iterations          6
% 3.00/1.04  --bmc1_ucm_extend_mode                  1
% 3.00/1.04  --bmc1_ucm_init_mode                    2
% 3.00/1.04  --bmc1_ucm_cone_mode                    none
% 3.00/1.04  --bmc1_ucm_reduced_relation_type        0
% 3.00/1.04  --bmc1_ucm_relax_model                  4
% 3.00/1.04  --bmc1_ucm_full_tr_after_sat            true
% 3.00/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/1.04  --bmc1_ucm_layered_model                none
% 3.00/1.04  --bmc1_ucm_max_lemma_size               10
% 3.00/1.04  
% 3.00/1.04  ------ AIG Options
% 3.00/1.04  
% 3.00/1.04  --aig_mode                              false
% 3.00/1.04  
% 3.00/1.04  ------ Instantiation Options
% 3.00/1.04  
% 3.00/1.04  --instantiation_flag                    true
% 3.00/1.04  --inst_sos_flag                         false
% 3.00/1.04  --inst_sos_phase                        true
% 3.00/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/1.04  --inst_lit_sel_side                     num_symb
% 3.00/1.04  --inst_solver_per_active                1400
% 3.00/1.04  --inst_solver_calls_frac                1.
% 3.00/1.04  --inst_passive_queue_type               priority_queues
% 3.00/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/1.04  --inst_passive_queues_freq              [25;2]
% 3.00/1.04  --inst_dismatching                      true
% 3.00/1.04  --inst_eager_unprocessed_to_passive     true
% 3.00/1.04  --inst_prop_sim_given                   true
% 3.00/1.04  --inst_prop_sim_new                     false
% 3.00/1.04  --inst_subs_new                         false
% 3.00/1.04  --inst_eq_res_simp                      false
% 3.00/1.04  --inst_subs_given                       false
% 3.00/1.04  --inst_orphan_elimination               true
% 3.00/1.04  --inst_learning_loop_flag               true
% 3.00/1.04  --inst_learning_start                   3000
% 3.00/1.04  --inst_learning_factor                  2
% 3.00/1.04  --inst_start_prop_sim_after_learn       3
% 3.00/1.04  --inst_sel_renew                        solver
% 3.00/1.04  --inst_lit_activity_flag                true
% 3.00/1.04  --inst_restr_to_given                   false
% 3.00/1.04  --inst_activity_threshold               500
% 3.00/1.04  --inst_out_proof                        true
% 3.00/1.04  
% 3.00/1.04  ------ Resolution Options
% 3.00/1.04  
% 3.00/1.04  --resolution_flag                       true
% 3.00/1.04  --res_lit_sel                           adaptive
% 3.00/1.04  --res_lit_sel_side                      none
% 3.00/1.04  --res_ordering                          kbo
% 3.00/1.04  --res_to_prop_solver                    active
% 3.00/1.04  --res_prop_simpl_new                    false
% 3.00/1.04  --res_prop_simpl_given                  true
% 3.00/1.04  --res_passive_queue_type                priority_queues
% 3.00/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/1.04  --res_passive_queues_freq               [15;5]
% 3.00/1.04  --res_forward_subs                      full
% 3.00/1.04  --res_backward_subs                     full
% 3.00/1.04  --res_forward_subs_resolution           true
% 3.00/1.04  --res_backward_subs_resolution          true
% 3.00/1.04  --res_orphan_elimination                true
% 3.00/1.04  --res_time_limit                        2.
% 3.00/1.04  --res_out_proof                         true
% 3.00/1.04  
% 3.00/1.04  ------ Superposition Options
% 3.00/1.04  
% 3.00/1.04  --superposition_flag                    true
% 3.00/1.04  --sup_passive_queue_type                priority_queues
% 3.00/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/1.04  --sup_passive_queues_freq               [8;1;4]
% 3.00/1.04  --demod_completeness_check              fast
% 3.00/1.04  --demod_use_ground                      true
% 3.00/1.04  --sup_to_prop_solver                    passive
% 3.00/1.04  --sup_prop_simpl_new                    true
% 3.00/1.04  --sup_prop_simpl_given                  true
% 3.00/1.04  --sup_fun_splitting                     false
% 3.00/1.04  --sup_smt_interval                      50000
% 3.00/1.04  
% 3.00/1.04  ------ Superposition Simplification Setup
% 3.00/1.04  
% 3.00/1.04  --sup_indices_passive                   []
% 3.00/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.04  --sup_full_bw                           [BwDemod]
% 3.00/1.04  --sup_immed_triv                        [TrivRules]
% 3.00/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.04  --sup_immed_bw_main                     []
% 3.00/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.04  
% 3.00/1.04  ------ Combination Options
% 3.00/1.04  
% 3.00/1.04  --comb_res_mult                         3
% 3.00/1.04  --comb_sup_mult                         2
% 3.00/1.04  --comb_inst_mult                        10
% 3.00/1.04  
% 3.00/1.04  ------ Debug Options
% 3.00/1.04  
% 3.00/1.04  --dbg_backtrace                         false
% 3.00/1.04  --dbg_dump_prop_clauses                 false
% 3.00/1.04  --dbg_dump_prop_clauses_file            -
% 3.00/1.04  --dbg_out_stat                          false
% 3.00/1.04  ------ Parsing...
% 3.00/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.00/1.04  
% 3.00/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.00/1.04  
% 3.00/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.00/1.04  
% 3.00/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.00/1.04  ------ Proving...
% 3.00/1.04  ------ Problem Properties 
% 3.00/1.04  
% 3.00/1.04  
% 3.00/1.04  clauses                                 22
% 3.00/1.04  conjectures                             4
% 3.00/1.04  EPR                                     3
% 3.00/1.04  Horn                                    17
% 3.00/1.04  unary                                   8
% 3.00/1.04  binary                                  7
% 3.00/1.04  lits                                    44
% 3.00/1.04  lits eq                                 16
% 3.00/1.04  fd_pure                                 0
% 3.00/1.04  fd_pseudo                               0
% 3.00/1.04  fd_cond                                 1
% 3.00/1.04  fd_pseudo_cond                          6
% 3.00/1.04  AC symbols                              0
% 3.00/1.04  
% 3.00/1.04  ------ Schedule dynamic 5 is on 
% 3.00/1.04  
% 3.00/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.00/1.04  
% 3.00/1.04  
% 3.00/1.04  ------ 
% 3.00/1.04  Current options:
% 3.00/1.04  ------ 
% 3.00/1.04  
% 3.00/1.04  ------ Input Options
% 3.00/1.04  
% 3.00/1.04  --out_options                           all
% 3.00/1.04  --tptp_safe_out                         true
% 3.00/1.04  --problem_path                          ""
% 3.00/1.04  --include_path                          ""
% 3.00/1.04  --clausifier                            res/vclausify_rel
% 3.00/1.04  --clausifier_options                    --mode clausify
% 3.00/1.04  --stdin                                 false
% 3.00/1.04  --stats_out                             all
% 3.00/1.04  
% 3.00/1.04  ------ General Options
% 3.00/1.04  
% 3.00/1.04  --fof                                   false
% 3.00/1.04  --time_out_real                         305.
% 3.00/1.04  --time_out_virtual                      -1.
% 3.00/1.04  --symbol_type_check                     false
% 3.00/1.04  --clausify_out                          false
% 3.00/1.04  --sig_cnt_out                           false
% 3.00/1.04  --trig_cnt_out                          false
% 3.00/1.04  --trig_cnt_out_tolerance                1.
% 3.00/1.04  --trig_cnt_out_sk_spl                   false
% 3.00/1.04  --abstr_cl_out                          false
% 3.00/1.04  
% 3.00/1.04  ------ Global Options
% 3.00/1.04  
% 3.00/1.04  --schedule                              default
% 3.00/1.04  --add_important_lit                     false
% 3.00/1.04  --prop_solver_per_cl                    1000
% 3.00/1.04  --min_unsat_core                        false
% 3.00/1.04  --soft_assumptions                      false
% 3.00/1.04  --soft_lemma_size                       3
% 3.00/1.04  --prop_impl_unit_size                   0
% 3.00/1.04  --prop_impl_unit                        []
% 3.00/1.04  --share_sel_clauses                     true
% 3.00/1.04  --reset_solvers                         false
% 3.00/1.04  --bc_imp_inh                            [conj_cone]
% 3.00/1.04  --conj_cone_tolerance                   3.
% 3.00/1.04  --extra_neg_conj                        none
% 3.00/1.04  --large_theory_mode                     true
% 3.00/1.04  --prolific_symb_bound                   200
% 3.00/1.04  --lt_threshold                          2000
% 3.00/1.04  --clause_weak_htbl                      true
% 3.00/1.04  --gc_record_bc_elim                     false
% 3.00/1.04  
% 3.00/1.04  ------ Preprocessing Options
% 3.00/1.04  
% 3.00/1.04  --preprocessing_flag                    true
% 3.00/1.04  --time_out_prep_mult                    0.1
% 3.00/1.04  --splitting_mode                        input
% 3.00/1.04  --splitting_grd                         true
% 3.00/1.04  --splitting_cvd                         false
% 3.00/1.04  --splitting_cvd_svl                     false
% 3.00/1.04  --splitting_nvd                         32
% 3.00/1.04  --sub_typing                            true
% 3.00/1.04  --prep_gs_sim                           true
% 3.00/1.04  --prep_unflatten                        true
% 3.00/1.04  --prep_res_sim                          true
% 3.00/1.04  --prep_upred                            true
% 3.00/1.04  --prep_sem_filter                       exhaustive
% 3.00/1.04  --prep_sem_filter_out                   false
% 3.00/1.04  --pred_elim                             true
% 3.00/1.04  --res_sim_input                         true
% 3.00/1.04  --eq_ax_congr_red                       true
% 3.00/1.04  --pure_diseq_elim                       true
% 3.00/1.04  --brand_transform                       false
% 3.00/1.04  --non_eq_to_eq                          false
% 3.00/1.04  --prep_def_merge                        true
% 3.00/1.04  --prep_def_merge_prop_impl              false
% 3.00/1.04  --prep_def_merge_mbd                    true
% 3.00/1.04  --prep_def_merge_tr_red                 false
% 3.00/1.04  --prep_def_merge_tr_cl                  false
% 3.00/1.04  --smt_preprocessing                     true
% 3.00/1.04  --smt_ac_axioms                         fast
% 3.00/1.04  --preprocessed_out                      false
% 3.00/1.04  --preprocessed_stats                    false
% 3.00/1.04  
% 3.00/1.04  ------ Abstraction refinement Options
% 3.00/1.04  
% 3.00/1.04  --abstr_ref                             []
% 3.00/1.04  --abstr_ref_prep                        false
% 3.00/1.04  --abstr_ref_until_sat                   false
% 3.00/1.04  --abstr_ref_sig_restrict                funpre
% 3.00/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/1.04  --abstr_ref_under                       []
% 3.00/1.04  
% 3.00/1.04  ------ SAT Options
% 3.00/1.04  
% 3.00/1.04  --sat_mode                              false
% 3.00/1.04  --sat_fm_restart_options                ""
% 3.00/1.04  --sat_gr_def                            false
% 3.00/1.04  --sat_epr_types                         true
% 3.00/1.04  --sat_non_cyclic_types                  false
% 3.00/1.04  --sat_finite_models                     false
% 3.00/1.04  --sat_fm_lemmas                         false
% 3.00/1.04  --sat_fm_prep                           false
% 3.00/1.04  --sat_fm_uc_incr                        true
% 3.00/1.04  --sat_out_model                         small
% 3.00/1.04  --sat_out_clauses                       false
% 3.00/1.04  
% 3.00/1.04  ------ QBF Options
% 3.00/1.04  
% 3.00/1.04  --qbf_mode                              false
% 3.00/1.04  --qbf_elim_univ                         false
% 3.00/1.04  --qbf_dom_inst                          none
% 3.00/1.04  --qbf_dom_pre_inst                      false
% 3.00/1.04  --qbf_sk_in                             false
% 3.00/1.04  --qbf_pred_elim                         true
% 3.00/1.04  --qbf_split                             512
% 3.00/1.04  
% 3.00/1.04  ------ BMC1 Options
% 3.00/1.04  
% 3.00/1.04  --bmc1_incremental                      false
% 3.00/1.04  --bmc1_axioms                           reachable_all
% 3.00/1.04  --bmc1_min_bound                        0
% 3.00/1.04  --bmc1_max_bound                        -1
% 3.00/1.04  --bmc1_max_bound_default                -1
% 3.00/1.04  --bmc1_symbol_reachability              true
% 3.00/1.04  --bmc1_property_lemmas                  false
% 3.00/1.04  --bmc1_k_induction                      false
% 3.00/1.04  --bmc1_non_equiv_states                 false
% 3.00/1.04  --bmc1_deadlock                         false
% 3.00/1.04  --bmc1_ucm                              false
% 3.00/1.04  --bmc1_add_unsat_core                   none
% 3.00/1.04  --bmc1_unsat_core_children              false
% 3.00/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/1.04  --bmc1_out_stat                         full
% 3.00/1.04  --bmc1_ground_init                      false
% 3.00/1.04  --bmc1_pre_inst_next_state              false
% 3.00/1.04  --bmc1_pre_inst_state                   false
% 3.00/1.04  --bmc1_pre_inst_reach_state             false
% 3.00/1.04  --bmc1_out_unsat_core                   false
% 3.00/1.04  --bmc1_aig_witness_out                  false
% 3.00/1.04  --bmc1_verbose                          false
% 3.00/1.04  --bmc1_dump_clauses_tptp                false
% 3.00/1.04  --bmc1_dump_unsat_core_tptp             false
% 3.00/1.04  --bmc1_dump_file                        -
% 3.00/1.04  --bmc1_ucm_expand_uc_limit              128
% 3.00/1.04  --bmc1_ucm_n_expand_iterations          6
% 3.00/1.04  --bmc1_ucm_extend_mode                  1
% 3.00/1.04  --bmc1_ucm_init_mode                    2
% 3.00/1.04  --bmc1_ucm_cone_mode                    none
% 3.00/1.04  --bmc1_ucm_reduced_relation_type        0
% 3.00/1.04  --bmc1_ucm_relax_model                  4
% 3.00/1.04  --bmc1_ucm_full_tr_after_sat            true
% 3.00/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/1.04  --bmc1_ucm_layered_model                none
% 3.00/1.04  --bmc1_ucm_max_lemma_size               10
% 3.00/1.04  
% 3.00/1.04  ------ AIG Options
% 3.00/1.04  
% 3.00/1.04  --aig_mode                              false
% 3.00/1.04  
% 3.00/1.04  ------ Instantiation Options
% 3.00/1.04  
% 3.00/1.04  --instantiation_flag                    true
% 3.00/1.04  --inst_sos_flag                         false
% 3.00/1.04  --inst_sos_phase                        true
% 3.00/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/1.04  --inst_lit_sel_side                     none
% 3.00/1.04  --inst_solver_per_active                1400
% 3.00/1.04  --inst_solver_calls_frac                1.
% 3.00/1.04  --inst_passive_queue_type               priority_queues
% 3.00/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/1.04  --inst_passive_queues_freq              [25;2]
% 3.00/1.04  --inst_dismatching                      true
% 3.00/1.04  --inst_eager_unprocessed_to_passive     true
% 3.00/1.04  --inst_prop_sim_given                   true
% 3.00/1.04  --inst_prop_sim_new                     false
% 3.00/1.04  --inst_subs_new                         false
% 3.00/1.04  --inst_eq_res_simp                      false
% 3.00/1.04  --inst_subs_given                       false
% 3.00/1.04  --inst_orphan_elimination               true
% 3.00/1.04  --inst_learning_loop_flag               true
% 3.00/1.04  --inst_learning_start                   3000
% 3.00/1.04  --inst_learning_factor                  2
% 3.00/1.04  --inst_start_prop_sim_after_learn       3
% 3.00/1.04  --inst_sel_renew                        solver
% 3.00/1.04  --inst_lit_activity_flag                true
% 3.00/1.04  --inst_restr_to_given                   false
% 3.00/1.04  --inst_activity_threshold               500
% 3.00/1.04  --inst_out_proof                        true
% 3.00/1.04  
% 3.00/1.04  ------ Resolution Options
% 3.00/1.04  
% 3.00/1.04  --resolution_flag                       false
% 3.00/1.04  --res_lit_sel                           adaptive
% 3.00/1.04  --res_lit_sel_side                      none
% 3.00/1.04  --res_ordering                          kbo
% 3.00/1.04  --res_to_prop_solver                    active
% 3.00/1.04  --res_prop_simpl_new                    false
% 3.00/1.04  --res_prop_simpl_given                  true
% 3.00/1.04  --res_passive_queue_type                priority_queues
% 3.00/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/1.04  --res_passive_queues_freq               [15;5]
% 3.00/1.04  --res_forward_subs                      full
% 3.00/1.04  --res_backward_subs                     full
% 3.00/1.04  --res_forward_subs_resolution           true
% 3.00/1.04  --res_backward_subs_resolution          true
% 3.00/1.04  --res_orphan_elimination                true
% 3.00/1.04  --res_time_limit                        2.
% 3.00/1.04  --res_out_proof                         true
% 3.00/1.04  
% 3.00/1.04  ------ Superposition Options
% 3.00/1.04  
% 3.00/1.04  --superposition_flag                    true
% 3.00/1.04  --sup_passive_queue_type                priority_queues
% 3.00/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/1.04  --sup_passive_queues_freq               [8;1;4]
% 3.00/1.04  --demod_completeness_check              fast
% 3.00/1.04  --demod_use_ground                      true
% 3.00/1.04  --sup_to_prop_solver                    passive
% 3.00/1.04  --sup_prop_simpl_new                    true
% 3.00/1.04  --sup_prop_simpl_given                  true
% 3.00/1.04  --sup_fun_splitting                     false
% 3.00/1.04  --sup_smt_interval                      50000
% 3.00/1.04  
% 3.00/1.04  ------ Superposition Simplification Setup
% 3.00/1.04  
% 3.00/1.04  --sup_indices_passive                   []
% 3.00/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.04  --sup_full_bw                           [BwDemod]
% 3.00/1.04  --sup_immed_triv                        [TrivRules]
% 3.00/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.04  --sup_immed_bw_main                     []
% 3.00/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.04  
% 3.00/1.04  ------ Combination Options
% 3.00/1.04  
% 3.00/1.04  --comb_res_mult                         3
% 3.00/1.04  --comb_sup_mult                         2
% 3.00/1.04  --comb_inst_mult                        10
% 3.00/1.04  
% 3.00/1.04  ------ Debug Options
% 3.00/1.04  
% 3.00/1.04  --dbg_backtrace                         false
% 3.00/1.04  --dbg_dump_prop_clauses                 false
% 3.00/1.04  --dbg_dump_prop_clauses_file            -
% 3.00/1.04  --dbg_out_stat                          false
% 3.00/1.04  
% 3.00/1.04  
% 3.00/1.04  
% 3.00/1.04  
% 3.00/1.04  ------ Proving...
% 3.00/1.04  
% 3.00/1.04  
% 3.00/1.04  % SZS status Theorem for theBenchmark.p
% 3.00/1.04  
% 3.00/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 3.00/1.04  
% 3.00/1.04  fof(f3,axiom,(
% 3.00/1.04    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.00/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.04  
% 3.00/1.04  fof(f15,plain,(
% 3.00/1.04    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.00/1.04    inference(ennf_transformation,[],[f3])).
% 3.00/1.04  
% 3.00/1.04  fof(f23,plain,(
% 3.00/1.04    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 3.00/1.04    introduced(choice_axiom,[])).
% 3.00/1.04  
% 3.00/1.04  fof(f24,plain,(
% 3.00/1.04    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 3.00/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f23])).
% 3.00/1.04  
% 3.00/1.04  fof(f41,plain,(
% 3.00/1.04    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 3.00/1.04    inference(cnf_transformation,[],[f24])).
% 3.00/1.04  
% 3.00/1.04  fof(f1,axiom,(
% 3.00/1.04    k1_xboole_0 = o_0_0_xboole_0),
% 3.00/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.04  
% 3.00/1.04  fof(f34,plain,(
% 3.00/1.04    k1_xboole_0 = o_0_0_xboole_0),
% 3.00/1.04    inference(cnf_transformation,[],[f1])).
% 3.00/1.04  
% 3.00/1.04  fof(f70,plain,(
% 3.00/1.04    ( ! [X0] : (r2_hidden(sK1(X0),X0) | o_0_0_xboole_0 = X0) )),
% 3.00/1.04    inference(definition_unfolding,[],[f41,f34])).
% 3.00/1.04  
% 3.00/1.04  fof(f13,conjecture,(
% 3.00/1.04    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 3.00/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.04  
% 3.00/1.04  fof(f14,negated_conjecture,(
% 3.00/1.04    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 3.00/1.04    inference(negated_conjecture,[],[f13])).
% 3.00/1.04  
% 3.00/1.04  fof(f17,plain,(
% 3.00/1.04    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 3.00/1.04    inference(ennf_transformation,[],[f14])).
% 3.00/1.04  
% 3.00/1.04  fof(f32,plain,(
% 3.00/1.04    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0)) => (k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & sK4 != sK5 & k2_xboole_0(sK4,sK5) = k1_tarski(sK3))),
% 3.00/1.04    introduced(choice_axiom,[])).
% 3.00/1.04  
% 3.00/1.04  fof(f33,plain,(
% 3.00/1.04    k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & sK4 != sK5 & k2_xboole_0(sK4,sK5) = k1_tarski(sK3)),
% 3.00/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f17,f32])).
% 3.00/1.04  
% 3.00/1.04  fof(f57,plain,(
% 3.00/1.04    k2_xboole_0(sK4,sK5) = k1_tarski(sK3)),
% 3.00/1.04    inference(cnf_transformation,[],[f33])).
% 3.00/1.04  
% 3.00/1.04  fof(f12,axiom,(
% 3.00/1.04    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.00/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.04  
% 3.00/1.04  fof(f56,plain,(
% 3.00/1.04    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.00/1.04    inference(cnf_transformation,[],[f12])).
% 3.00/1.04  
% 3.00/1.04  fof(f62,plain,(
% 3.00/1.04    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 3.00/1.04    inference(definition_unfolding,[],[f56,f61])).
% 3.00/1.04  
% 3.00/1.04  fof(f7,axiom,(
% 3.00/1.04    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.00/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.04  
% 3.00/1.04  fof(f48,plain,(
% 3.00/1.04    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.00/1.04    inference(cnf_transformation,[],[f7])).
% 3.00/1.04  
% 3.00/1.04  fof(f8,axiom,(
% 3.00/1.04    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.00/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.04  
% 3.00/1.04  fof(f49,plain,(
% 3.00/1.04    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.00/1.04    inference(cnf_transformation,[],[f8])).
% 3.00/1.04  
% 3.00/1.04  fof(f9,axiom,(
% 3.00/1.04    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.00/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.04  
% 3.00/1.04  fof(f50,plain,(
% 3.00/1.04    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.00/1.04    inference(cnf_transformation,[],[f9])).
% 3.00/1.04  
% 3.00/1.04  fof(f61,plain,(
% 3.00/1.04    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.00/1.04    inference(definition_unfolding,[],[f49,f50])).
% 3.00/1.04  
% 3.00/1.04  fof(f63,plain,(
% 3.00/1.04    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.00/1.04    inference(definition_unfolding,[],[f48,f61])).
% 3.00/1.04  
% 3.00/1.04  fof(f84,plain,(
% 3.00/1.04    k2_enumset1(sK3,sK3,sK3,sK3) = k3_tarski(k2_enumset1(sK4,sK4,sK4,sK5))),
% 3.00/1.04    inference(definition_unfolding,[],[f57,f62,f63])).
% 3.00/1.04  
% 3.00/1.04  fof(f5,axiom,(
% 3.00/1.04    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.00/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.04  
% 3.00/1.04  fof(f43,plain,(
% 3.00/1.04    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.00/1.04    inference(cnf_transformation,[],[f5])).
% 3.00/1.04  
% 3.00/1.04  fof(f72,plain,(
% 3.00/1.04    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 3.00/1.04    inference(definition_unfolding,[],[f43,f62])).
% 3.00/1.04  
% 3.00/1.04  fof(f11,axiom,(
% 3.00/1.04    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.00/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.04  
% 3.00/1.04  fof(f30,plain,(
% 3.00/1.04    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.00/1.04    inference(nnf_transformation,[],[f11])).
% 3.00/1.04  
% 3.00/1.04  fof(f31,plain,(
% 3.00/1.04    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.00/1.04    inference(flattening,[],[f30])).
% 3.00/1.04  
% 3.00/1.04  fof(f53,plain,(
% 3.00/1.04    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 3.00/1.04    inference(cnf_transformation,[],[f31])).
% 3.00/1.04  
% 3.00/1.04  fof(f81,plain,(
% 3.00/1.04    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) = X0 | o_0_0_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 3.00/1.04    inference(definition_unfolding,[],[f53,f63,f34,f63])).
% 3.00/1.04  
% 3.00/1.04  fof(f59,plain,(
% 3.00/1.04    k1_xboole_0 != sK4),
% 3.00/1.04    inference(cnf_transformation,[],[f33])).
% 3.00/1.04  
% 3.00/1.04  fof(f83,plain,(
% 3.00/1.04    o_0_0_xboole_0 != sK4),
% 3.00/1.04    inference(definition_unfolding,[],[f59,f34])).
% 3.00/1.04  
% 3.00/1.04  fof(f6,axiom,(
% 3.00/1.04    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.00/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.04  
% 3.00/1.04  fof(f25,plain,(
% 3.00/1.04    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.00/1.04    inference(nnf_transformation,[],[f6])).
% 3.00/1.04  
% 3.00/1.04  fof(f26,plain,(
% 3.00/1.04    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.00/1.04    inference(rectify,[],[f25])).
% 3.00/1.04  
% 3.00/1.04  fof(f27,plain,(
% 3.00/1.04    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 3.00/1.04    introduced(choice_axiom,[])).
% 3.00/1.04  
% 3.00/1.04  fof(f28,plain,(
% 3.00/1.04    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.00/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).
% 3.00/1.04  
% 3.00/1.04  fof(f44,plain,(
% 3.00/1.04    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.00/1.04    inference(cnf_transformation,[],[f28])).
% 3.00/1.04  
% 3.00/1.04  fof(f76,plain,(
% 3.00/1.04    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 3.00/1.04    inference(definition_unfolding,[],[f44,f63])).
% 3.00/1.04  
% 3.00/1.04  fof(f90,plain,(
% 3.00/1.04    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 3.00/1.04    inference(equality_resolution,[],[f76])).
% 3.00/1.04  
% 3.00/1.04  fof(f45,plain,(
% 3.00/1.04    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.00/1.04    inference(cnf_transformation,[],[f28])).
% 3.00/1.04  
% 3.00/1.04  fof(f75,plain,(
% 3.00/1.04    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 3.00/1.04    inference(definition_unfolding,[],[f45,f63])).
% 3.00/1.04  
% 3.00/1.04  fof(f88,plain,(
% 3.00/1.04    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 3.00/1.04    inference(equality_resolution,[],[f75])).
% 3.00/1.04  
% 3.00/1.04  fof(f89,plain,(
% 3.00/1.04    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 3.00/1.04    inference(equality_resolution,[],[f88])).
% 3.00/1.04  
% 3.00/1.04  fof(f2,axiom,(
% 3.00/1.04    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.00/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.04  
% 3.00/1.04  fof(f18,plain,(
% 3.00/1.04    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.00/1.04    inference(nnf_transformation,[],[f2])).
% 3.00/1.04  
% 3.00/1.04  fof(f19,plain,(
% 3.00/1.04    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.00/1.04    inference(flattening,[],[f18])).
% 3.00/1.04  
% 3.00/1.04  fof(f20,plain,(
% 3.00/1.04    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.00/1.04    inference(rectify,[],[f19])).
% 3.00/1.04  
% 3.00/1.04  fof(f21,plain,(
% 3.00/1.04    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.00/1.04    introduced(choice_axiom,[])).
% 3.00/1.04  
% 3.00/1.04  fof(f22,plain,(
% 3.00/1.04    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.00/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).
% 3.00/1.04  
% 3.00/1.04  fof(f37,plain,(
% 3.00/1.04    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 3.00/1.04    inference(cnf_transformation,[],[f22])).
% 3.00/1.04  
% 3.00/1.04  fof(f67,plain,(
% 3.00/1.04    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k2_enumset1(X0,X0,X0,X1)) != X2) )),
% 3.00/1.04    inference(definition_unfolding,[],[f37,f62])).
% 3.00/1.04  
% 3.00/1.04  fof(f85,plain,(
% 3.00/1.04    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k2_enumset1(X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 3.00/1.04    inference(equality_resolution,[],[f67])).
% 3.00/1.04  
% 3.00/1.04  fof(f60,plain,(
% 3.00/1.04    k1_xboole_0 != sK5),
% 3.00/1.04    inference(cnf_transformation,[],[f33])).
% 3.00/1.04  
% 3.00/1.04  fof(f82,plain,(
% 3.00/1.04    o_0_0_xboole_0 != sK5),
% 3.00/1.04    inference(definition_unfolding,[],[f60,f34])).
% 3.00/1.04  
% 3.00/1.04  fof(f38,plain,(
% 3.00/1.04    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.00/1.04    inference(cnf_transformation,[],[f22])).
% 3.00/1.04  
% 3.00/1.04  fof(f66,plain,(
% 3.00/1.04    ( ! [X2,X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.00/1.04    inference(definition_unfolding,[],[f38,f62])).
% 3.00/1.04  
% 3.00/1.04  fof(f58,plain,(
% 3.00/1.04    sK4 != sK5),
% 3.00/1.04    inference(cnf_transformation,[],[f33])).
% 3.00/1.04  
% 3.00/1.04  fof(f40,plain,(
% 3.00/1.04    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.00/1.04    inference(cnf_transformation,[],[f22])).
% 3.00/1.04  
% 3.00/1.04  fof(f64,plain,(
% 3.00/1.04    ( ! [X2,X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.00/1.04    inference(definition_unfolding,[],[f40,f62])).
% 3.00/1.04  
% 3.00/1.04  cnf(c_6,plain,
% 3.00/1.04      ( r2_hidden(sK1(X0),X0) | o_0_0_xboole_0 = X0 ),
% 3.00/1.04      inference(cnf_transformation,[],[f70]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_788,plain,
% 3.00/1.04      ( o_0_0_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 3.00/1.04      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_21,negated_conjecture,
% 3.00/1.04      ( k2_enumset1(sK3,sK3,sK3,sK3) = k3_tarski(k2_enumset1(sK4,sK4,sK4,sK5)) ),
% 3.00/1.04      inference(cnf_transformation,[],[f84]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_8,plain,
% 3.00/1.04      ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
% 3.00/1.04      inference(cnf_transformation,[],[f72]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_786,plain,
% 3.00/1.04      ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = iProver_top ),
% 3.00/1.04      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_1066,plain,
% 3.00/1.04      ( r1_tarski(sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
% 3.00/1.04      inference(superposition,[status(thm)],[c_21,c_786]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_17,plain,
% 3.00/1.04      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
% 3.00/1.04      | k2_enumset1(X1,X1,X1,X1) = X0
% 3.00/1.04      | o_0_0_xboole_0 = X0 ),
% 3.00/1.04      inference(cnf_transformation,[],[f81]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_777,plain,
% 3.00/1.04      ( k2_enumset1(X0,X0,X0,X0) = X1
% 3.00/1.04      | o_0_0_xboole_0 = X1
% 3.00/1.04      | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 3.00/1.04      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_1272,plain,
% 3.00/1.04      ( k2_enumset1(sK3,sK3,sK3,sK3) = sK4 | sK4 = o_0_0_xboole_0 ),
% 3.00/1.04      inference(superposition,[status(thm)],[c_1066,c_777]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_19,negated_conjecture,
% 3.00/1.04      ( o_0_0_xboole_0 != sK4 ),
% 3.00/1.04      inference(cnf_transformation,[],[f83]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_12,plain,
% 3.00/1.04      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 3.00/1.04      inference(cnf_transformation,[],[f90]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_38,plain,
% 3.00/1.04      ( ~ r2_hidden(o_0_0_xboole_0,k2_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))
% 3.00/1.04      | o_0_0_xboole_0 = o_0_0_xboole_0 ),
% 3.00/1.04      inference(instantiation,[status(thm)],[c_12]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_11,plain,
% 3.00/1.04      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
% 3.00/1.04      inference(cnf_transformation,[],[f89]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_41,plain,
% 3.00/1.04      ( r2_hidden(o_0_0_xboole_0,k2_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) ),
% 3.00/1.04      inference(instantiation,[status(thm)],[c_11]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_363,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_931,plain,
% 3.00/1.04      ( sK4 != X0 | o_0_0_xboole_0 != X0 | o_0_0_xboole_0 = sK4 ),
% 3.00/1.04      inference(instantiation,[status(thm)],[c_363]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_932,plain,
% 3.00/1.04      ( sK4 != o_0_0_xboole_0
% 3.00/1.04      | o_0_0_xboole_0 = sK4
% 3.00/1.04      | o_0_0_xboole_0 != o_0_0_xboole_0 ),
% 3.00/1.04      inference(instantiation,[status(thm)],[c_931]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_1627,plain,
% 3.00/1.04      ( k2_enumset1(sK3,sK3,sK3,sK3) = sK4 ),
% 3.00/1.04      inference(global_propositional_subsumption,
% 3.00/1.04                [status(thm)],
% 3.00/1.04                [c_1272,c_19,c_38,c_41,c_932]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_1632,plain,
% 3.00/1.04      ( k3_tarski(k2_enumset1(sK4,sK4,sK4,sK5)) = sK4 ),
% 3.00/1.04      inference(demodulation,[status(thm)],[c_1627,c_21]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_3,plain,
% 3.00/1.04      ( ~ r2_hidden(X0,X1)
% 3.00/1.04      | r2_hidden(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) ),
% 3.00/1.04      inference(cnf_transformation,[],[f85]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_791,plain,
% 3.00/1.04      ( r2_hidden(X0,X1) != iProver_top
% 3.00/1.04      | r2_hidden(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) = iProver_top ),
% 3.00/1.04      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_2069,plain,
% 3.00/1.04      ( r2_hidden(X0,sK4) = iProver_top
% 3.00/1.04      | r2_hidden(X0,sK5) != iProver_top ),
% 3.00/1.04      inference(superposition,[status(thm)],[c_1632,c_791]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_2234,plain,
% 3.00/1.04      ( sK5 = o_0_0_xboole_0 | r2_hidden(sK1(sK5),sK4) = iProver_top ),
% 3.00/1.04      inference(superposition,[status(thm)],[c_788,c_2069]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_18,negated_conjecture,
% 3.00/1.04      ( o_0_0_xboole_0 != sK5 ),
% 3.00/1.04      inference(cnf_transformation,[],[f82]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_929,plain,
% 3.00/1.04      ( sK5 != X0 | o_0_0_xboole_0 != X0 | o_0_0_xboole_0 = sK5 ),
% 3.00/1.04      inference(instantiation,[status(thm)],[c_363]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_930,plain,
% 3.00/1.04      ( sK5 != o_0_0_xboole_0
% 3.00/1.04      | o_0_0_xboole_0 = sK5
% 3.00/1.04      | o_0_0_xboole_0 != o_0_0_xboole_0 ),
% 3.00/1.04      inference(instantiation,[status(thm)],[c_929]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_2553,plain,
% 3.00/1.04      ( r2_hidden(sK1(sK5),sK4) = iProver_top ),
% 3.00/1.04      inference(global_propositional_subsumption,
% 3.00/1.04                [status(thm)],
% 3.00/1.04                [c_2234,c_18,c_38,c_41,c_930]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_782,plain,
% 3.00/1.04      ( X0 = X1 | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
% 3.00/1.04      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_1646,plain,
% 3.00/1.04      ( sK3 = X0 | r2_hidden(X0,sK4) != iProver_top ),
% 3.00/1.04      inference(superposition,[status(thm)],[c_1627,c_782]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_2558,plain,
% 3.00/1.04      ( sK1(sK5) = sK3 ),
% 3.00/1.04      inference(superposition,[status(thm)],[c_2553,c_1646]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_7041,plain,
% 3.00/1.04      ( sK5 = o_0_0_xboole_0 | r2_hidden(sK3,sK5) = iProver_top ),
% 3.00/1.04      inference(superposition,[status(thm)],[c_2558,c_788]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_2,plain,
% 3.00/1.04      ( r2_hidden(sK0(X0,X1,X2),X1)
% 3.00/1.04      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.00/1.04      | r2_hidden(sK0(X0,X1,X2),X0)
% 3.00/1.04      | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2 ),
% 3.00/1.04      inference(cnf_transformation,[],[f66]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_792,plain,
% 3.00/1.04      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2
% 3.00/1.04      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
% 3.00/1.04      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 3.00/1.04      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top ),
% 3.00/1.04      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_3172,plain,
% 3.00/1.04      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = sK5
% 3.00/1.04      | r2_hidden(sK0(X0,X1,sK5),X1) = iProver_top
% 3.00/1.04      | r2_hidden(sK0(X0,X1,sK5),X0) = iProver_top
% 3.00/1.04      | r2_hidden(sK0(X0,X1,sK5),sK4) = iProver_top ),
% 3.00/1.04      inference(superposition,[status(thm)],[c_792,c_2069]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_4162,plain,
% 3.00/1.04      ( k3_tarski(k2_enumset1(X0,X0,X0,sK5)) = sK5
% 3.00/1.04      | r2_hidden(sK0(X0,sK5,sK5),X0) = iProver_top
% 3.00/1.04      | r2_hidden(sK0(X0,sK5,sK5),sK4) = iProver_top ),
% 3.00/1.04      inference(superposition,[status(thm)],[c_3172,c_2069]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_4308,plain,
% 3.00/1.04      ( k3_tarski(k2_enumset1(sK4,sK4,sK4,sK5)) = sK5
% 3.00/1.04      | r2_hidden(sK0(sK4,sK5,sK5),sK4) = iProver_top
% 3.00/1.04      | iProver_top != iProver_top ),
% 3.00/1.04      inference(equality_factoring,[status(thm)],[c_4162]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_4310,plain,
% 3.00/1.04      ( k3_tarski(k2_enumset1(sK4,sK4,sK4,sK5)) = sK5
% 3.00/1.04      | r2_hidden(sK0(sK4,sK5,sK5),sK4) = iProver_top ),
% 3.00/1.04      inference(equality_resolution_simp,[status(thm)],[c_4308]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_4313,plain,
% 3.00/1.04      ( sK4 = sK5 | r2_hidden(sK0(sK4,sK5,sK5),sK4) = iProver_top ),
% 3.00/1.04      inference(demodulation,[status(thm)],[c_4310,c_1632]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_20,negated_conjecture,
% 3.00/1.04      ( sK4 != sK5 ),
% 3.00/1.04      inference(cnf_transformation,[],[f58]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_4546,plain,
% 3.00/1.04      ( r2_hidden(sK0(sK4,sK5,sK5),sK4) = iProver_top ),
% 3.00/1.04      inference(global_propositional_subsumption,
% 3.00/1.04                [status(thm)],
% 3.00/1.04                [c_4313,c_20]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_4551,plain,
% 3.00/1.04      ( sK0(sK4,sK5,sK5) = sK3 ),
% 3.00/1.04      inference(superposition,[status(thm)],[c_4546,c_1646]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_0,plain,
% 3.00/1.04      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 3.00/1.04      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 3.00/1.04      | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2 ),
% 3.00/1.04      inference(cnf_transformation,[],[f64]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_794,plain,
% 3.00/1.04      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2
% 3.00/1.04      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
% 3.00/1.04      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top ),
% 3.00/1.04      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_4867,plain,
% 3.00/1.04      ( k3_tarski(k2_enumset1(sK4,sK4,sK4,sK5)) = sK5
% 3.00/1.04      | r2_hidden(sK0(sK4,sK5,sK5),sK5) != iProver_top
% 3.00/1.04      | r2_hidden(sK3,sK5) != iProver_top ),
% 3.00/1.04      inference(superposition,[status(thm)],[c_4551,c_794]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_4890,plain,
% 3.00/1.04      ( k3_tarski(k2_enumset1(sK4,sK4,sK4,sK5)) = sK5
% 3.00/1.04      | r2_hidden(sK3,sK5) != iProver_top ),
% 3.00/1.04      inference(light_normalisation,[status(thm)],[c_4867,c_4551]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(c_4891,plain,
% 3.00/1.04      ( sK4 = sK5 | r2_hidden(sK3,sK5) != iProver_top ),
% 3.00/1.04      inference(demodulation,[status(thm)],[c_4890,c_1632]) ).
% 3.00/1.04  
% 3.00/1.04  cnf(contradiction,plain,
% 3.00/1.04      ( $false ),
% 3.00/1.04      inference(minisat,
% 3.00/1.04                [status(thm)],
% 3.00/1.04                [c_7041,c_4891,c_930,c_41,c_38,c_18,c_20]) ).
% 3.00/1.04  
% 3.00/1.04  
% 3.00/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 3.00/1.04  
% 3.00/1.04  ------                               Statistics
% 3.00/1.04  
% 3.00/1.04  ------ General
% 3.00/1.04  
% 3.00/1.04  abstr_ref_over_cycles:                  0
% 3.00/1.04  abstr_ref_under_cycles:                 0
% 3.00/1.04  gc_basic_clause_elim:                   0
% 3.00/1.04  forced_gc_time:                         0
% 3.00/1.04  parsing_time:                           0.011
% 3.00/1.04  unif_index_cands_time:                  0.
% 3.00/1.04  unif_index_add_time:                    0.
% 3.00/1.04  orderings_time:                         0.
% 3.00/1.04  out_proof_time:                         0.023
% 3.00/1.04  total_time:                             0.316
% 3.00/1.04  num_of_symbols:                         42
% 3.00/1.04  num_of_terms:                           6691
% 3.00/1.04  
% 3.00/1.04  ------ Preprocessing
% 3.00/1.04  
% 3.00/1.04  num_of_splits:                          0
% 3.00/1.04  num_of_split_atoms:                     0
% 3.00/1.04  num_of_reused_defs:                     0
% 3.00/1.04  num_eq_ax_congr_red:                    12
% 3.00/1.04  num_of_sem_filtered_clauses:            1
% 3.00/1.04  num_of_subtypes:                        0
% 3.00/1.04  monotx_restored_types:                  0
% 3.00/1.04  sat_num_of_epr_types:                   0
% 3.00/1.04  sat_num_of_non_cyclic_types:            0
% 3.00/1.04  sat_guarded_non_collapsed_types:        0
% 3.00/1.04  num_pure_diseq_elim:                    0
% 3.00/1.04  simp_replaced_by:                       0
% 3.00/1.04  res_preprocessed:                       79
% 3.00/1.04  prep_upred:                             0
% 3.00/1.04  prep_unflattend:                        17
% 3.00/1.04  smt_new_axioms:                         0
% 3.00/1.04  pred_elim_cands:                        2
% 3.00/1.04  pred_elim:                              0
% 3.00/1.04  pred_elim_cl:                           0
% 3.00/1.04  pred_elim_cycles:                       1
% 3.00/1.04  merged_defs:                            6
% 3.00/1.04  merged_defs_ncl:                        0
% 3.00/1.04  bin_hyper_res:                          6
% 3.00/1.04  prep_cycles:                            3
% 3.00/1.04  pred_elim_time:                         0.003
% 3.00/1.04  splitting_time:                         0.
% 3.00/1.04  sem_filter_time:                        0.
% 3.00/1.04  monotx_time:                            0.001
% 3.00/1.04  subtype_inf_time:                       0.
% 3.00/1.04  
% 3.00/1.04  ------ Problem properties
% 3.00/1.04  
% 3.00/1.04  clauses:                                22
% 3.00/1.04  conjectures:                            4
% 3.00/1.04  epr:                                    3
% 3.00/1.04  horn:                                   17
% 3.00/1.04  ground:                                 4
% 3.00/1.04  unary:                                  8
% 3.00/1.04  binary:                                 7
% 3.00/1.04  lits:                                   44
% 3.00/1.04  lits_eq:                                16
% 3.00/1.04  fd_pure:                                0
% 3.00/1.04  fd_pseudo:                              0
% 3.00/1.04  fd_cond:                                1
% 3.00/1.04  fd_pseudo_cond:                         6
% 3.00/1.04  ac_symbols:                             0
% 3.00/1.04  
% 3.00/1.04  ------ Propositional Solver
% 3.00/1.04  
% 3.00/1.04  prop_solver_calls:                      25
% 3.00/1.04  prop_fast_solver_calls:                 510
% 3.00/1.04  smt_solver_calls:                       0
% 3.00/1.04  smt_fast_solver_calls:                  0
% 3.00/1.04  prop_num_of_clauses:                    2798
% 3.00/1.04  prop_preprocess_simplified:             5410
% 3.00/1.04  prop_fo_subsumed:                       6
% 3.00/1.04  prop_solver_time:                       0.
% 3.00/1.04  smt_solver_time:                        0.
% 3.00/1.04  smt_fast_solver_time:                   0.
% 3.00/1.04  prop_fast_solver_time:                  0.
% 3.00/1.04  prop_unsat_core_time:                   0.
% 3.00/1.04  
% 3.00/1.04  ------ QBF
% 3.00/1.04  
% 3.00/1.04  qbf_q_res:                              0
% 3.00/1.04  qbf_num_tautologies:                    0
% 3.00/1.04  qbf_prep_cycles:                        0
% 3.00/1.04  
% 3.00/1.04  ------ BMC1
% 3.00/1.04  
% 3.00/1.04  bmc1_current_bound:                     -1
% 3.00/1.04  bmc1_last_solved_bound:                 -1
% 3.00/1.04  bmc1_unsat_core_size:                   -1
% 3.00/1.04  bmc1_unsat_core_parents_size:           -1
% 3.00/1.04  bmc1_merge_next_fun:                    0
% 3.00/1.04  bmc1_unsat_core_clauses_time:           0.
% 3.00/1.04  
% 3.00/1.04  ------ Instantiation
% 3.00/1.04  
% 3.00/1.04  inst_num_of_clauses:                    706
% 3.00/1.04  inst_num_in_passive:                    206
% 3.00/1.04  inst_num_in_active:                     305
% 3.00/1.04  inst_num_in_unprocessed:                195
% 3.00/1.04  inst_num_of_loops:                      350
% 3.00/1.04  inst_num_of_learning_restarts:          0
% 3.00/1.04  inst_num_moves_active_passive:          42
% 3.00/1.04  inst_lit_activity:                      0
% 3.00/1.04  inst_lit_activity_moves:                0
% 3.00/1.04  inst_num_tautologies:                   0
% 3.00/1.04  inst_num_prop_implied:                  0
% 3.00/1.04  inst_num_existing_simplified:           0
% 3.00/1.04  inst_num_eq_res_simplified:             0
% 3.00/1.04  inst_num_child_elim:                    0
% 3.00/1.04  inst_num_of_dismatching_blockings:      277
% 3.00/1.04  inst_num_of_non_proper_insts:           824
% 3.00/1.04  inst_num_of_duplicates:                 0
% 3.00/1.04  inst_inst_num_from_inst_to_res:         0
% 3.00/1.04  inst_dismatching_checking_time:         0.
% 3.00/1.04  
% 3.00/1.04  ------ Resolution
% 3.00/1.04  
% 3.00/1.04  res_num_of_clauses:                     0
% 3.00/1.04  res_num_in_passive:                     0
% 3.00/1.04  res_num_in_active:                      0
% 3.00/1.04  res_num_of_loops:                       82
% 3.00/1.04  res_forward_subset_subsumed:            39
% 3.00/1.04  res_backward_subset_subsumed:           0
% 3.00/1.04  res_forward_subsumed:                   0
% 3.00/1.04  res_backward_subsumed:                  0
% 3.00/1.04  res_forward_subsumption_resolution:     0
% 3.00/1.04  res_backward_subsumption_resolution:    0
% 3.00/1.04  res_clause_to_clause_subsumption:       981
% 3.00/1.04  res_orphan_elimination:                 0
% 3.00/1.04  res_tautology_del:                      25
% 3.00/1.04  res_num_eq_res_simplified:              0
% 3.00/1.04  res_num_sel_changes:                    0
% 3.00/1.04  res_moves_from_active_to_pass:          0
% 3.00/1.04  
% 3.00/1.04  ------ Superposition
% 3.00/1.04  
% 3.00/1.04  sup_time_total:                         0.
% 3.00/1.04  sup_time_generating:                    0.
% 3.00/1.04  sup_time_sim_full:                      0.
% 3.00/1.04  sup_time_sim_immed:                     0.
% 3.00/1.04  
% 3.00/1.04  sup_num_of_clauses:                     191
% 3.00/1.04  sup_num_in_active:                      64
% 3.00/1.04  sup_num_in_passive:                     127
% 3.00/1.04  sup_num_of_loops:                       69
% 3.00/1.04  sup_fw_superposition:                   113
% 3.00/1.04  sup_bw_superposition:                   207
% 3.00/1.04  sup_immediate_simplified:               78
% 3.00/1.04  sup_given_eliminated:                   1
% 3.00/1.04  comparisons_done:                       0
% 3.00/1.04  comparisons_avoided:                    12
% 3.00/1.04  
% 3.00/1.04  ------ Simplifications
% 3.00/1.04  
% 3.00/1.04  
% 3.00/1.04  sim_fw_subset_subsumed:                 60
% 3.00/1.04  sim_bw_subset_subsumed:                 1
% 3.00/1.04  sim_fw_subsumed:                        18
% 3.00/1.04  sim_bw_subsumed:                        1
% 3.00/1.04  sim_fw_subsumption_res:                 1
% 3.00/1.04  sim_bw_subsumption_res:                 0
% 3.00/1.04  sim_tautology_del:                      29
% 3.00/1.04  sim_eq_tautology_del:                   15
% 3.00/1.04  sim_eq_res_simp:                        35
% 3.00/1.04  sim_fw_demodulated:                     18
% 3.00/1.04  sim_bw_demodulated:                     6
% 3.00/1.04  sim_light_normalised:                   13
% 3.00/1.04  sim_joinable_taut:                      0
% 3.00/1.04  sim_joinable_simp:                      0
% 3.00/1.04  sim_ac_normalised:                      0
% 3.00/1.04  sim_smt_subsumption:                    0
% 3.00/1.04  
%------------------------------------------------------------------------------
