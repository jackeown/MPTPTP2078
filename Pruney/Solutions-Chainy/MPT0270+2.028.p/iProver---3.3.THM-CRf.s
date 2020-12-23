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
% DateTime   : Thu Dec  3 11:36:00 EST 2020

% Result     : Theorem 11.97s
% Output     : CNFRefutation 11.97s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 314 expanded)
%              Number of clauses        :   49 (  79 expanded)
%              Number of leaves         :   16 (  78 expanded)
%              Depth                    :   15
%              Number of atoms          :  278 (1217 expanded)
%              Number of equality atoms :  123 ( 367 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f71,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f38,f58,f58])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f58])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f87,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f88,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f5,axiom,(
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
    inference(nnf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f89,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f60,f67])).

fof(f69,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f59,f68])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f64,f69])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      <=> ~ r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
    <~> ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) )
      & ( ~ r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f36,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X0,X1)
          | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) )
        & ( ~ r2_hidden(X0,X1)
          | k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) ) )
   => ( ( r2_hidden(sK3,sK4)
        | k4_xboole_0(k1_tarski(sK3),sK4) != k1_tarski(sK3) )
      & ( ~ r2_hidden(sK3,sK4)
        | k4_xboole_0(k1_tarski(sK3),sK4) = k1_tarski(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ( r2_hidden(sK3,sK4)
      | k4_xboole_0(k1_tarski(sK3),sK4) != k1_tarski(sK3) )
    & ( ~ r2_hidden(sK3,sK4)
      | k4_xboole_0(k1_tarski(sK3),sK4) = k1_tarski(sK3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f35,f36])).

fof(f65,plain,
    ( ~ r2_hidden(sK3,sK4)
    | k4_xboole_0(k1_tarski(sK3),sK4) = k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f82,plain,
    ( ~ r2_hidden(sK3,sK4)
    | k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f65,f69,f69])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f63,f69])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f66,plain,
    ( r2_hidden(sK3,sK4)
    | k4_xboole_0(k1_tarski(sK3),sK4) != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f81,plain,
    ( r2_hidden(sK3,sK4)
    | k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4) != k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f66,f69,f69])).

cnf(c_497,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1272,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),sK4)
    | X0 != sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | X1 != sK4 ),
    inference(instantiation,[status(thm)],[c_497])).

cnf(c_1849,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,X2))
    | ~ r2_hidden(sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),sK4)
    | X0 != sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | k4_xboole_0(X1,X2) != sK4 ),
    inference(instantiation,[status(thm)],[c_1272])).

cnf(c_12581,plain,
    ( r2_hidden(sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k4_xboole_0(X0,X1))
    | ~ r2_hidden(sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),sK4)
    | sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | k4_xboole_0(X0,X1) != sK4 ),
    inference(instantiation,[status(thm)],[c_1849])).

cnf(c_50552,plain,
    ( r2_hidden(sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k4_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))
    | ~ r2_hidden(sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),sK4)
    | sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | k4_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != sK4 ),
    inference(instantiation,[status(thm)],[c_12581])).

cnf(c_10,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_994,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_9,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_995,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3735,plain,
    ( k4_xboole_0(X0,X0) = X1
    | r2_hidden(sK1(X0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_994,c_995])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_19,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_986,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_987,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1307,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_986,c_987])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_992,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1775,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top
    | r2_hidden(X0,k4_xboole_0(k4_xboole_0(X1,X2),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1307,c_992])).

cnf(c_13,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_991,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_23109,plain,
    ( r2_hidden(X0,k4_xboole_0(k4_xboole_0(X1,X2),X1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1775,c_991])).

cnf(c_23133,plain,
    ( r2_hidden(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_23109])).

cnf(c_24255,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k4_xboole_0(X2,X2) ),
    inference(superposition,[status(thm)],[c_3735,c_23133])).

cnf(c_16,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_988,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1306,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_988,c_987])).

cnf(c_24906,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2)) = X0 ),
    inference(superposition,[status(thm)],[c_24255,c_1306])).

cnf(c_20,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X0)) = X1 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_985,plain,
    ( k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) = X0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_23,negated_conjecture,
    ( ~ r2_hidden(sK3,sK4)
    | k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_982,plain,
    ( k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
    | r2_hidden(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2471,plain,
    ( k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
    | k4_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = sK4 ),
    inference(superposition,[status(thm)],[c_985,c_982])).

cnf(c_1774,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1307,c_1])).

cnf(c_2046,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_1774])).

cnf(c_2562,plain,
    ( k4_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = sK4
    | k4_xboole_0(sK4,k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k4_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(superposition,[status(thm)],[c_2471,c_2046])).

cnf(c_24957,plain,
    ( k4_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = sK4
    | k4_xboole_0(sK4,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(superposition,[status(thm)],[c_24255,c_2562])).

cnf(c_26899,plain,
    ( k4_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = sK4 ),
    inference(demodulation,[status(thm)],[c_24906,c_24957])).

cnf(c_493,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3163,plain,
    ( sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_493])).

cnf(c_1247,plain,
    ( ~ r2_hidden(sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | ~ r2_hidden(sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k4_xboole_0(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1632,plain,
    ( ~ r2_hidden(sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | ~ r2_hidden(sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k4_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
    inference(instantiation,[status(thm)],[c_1247])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X0)) != X1 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1190,plain,
    ( ~ r2_hidden(sK3,sK4)
    | k4_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != sK4 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_8,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X0)
    | ~ r2_hidden(sK1(X0,X1,X2),X2)
    | r2_hidden(sK1(X0,X1,X2),X1)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1169,plain,
    ( ~ r2_hidden(sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | r2_hidden(sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),sK4)
    | k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1166,plain,
    ( r2_hidden(sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_22,negated_conjecture,
    ( r2_hidden(sK3,sK4)
    | k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4) != k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_50552,c_26899,c_3163,c_1632,c_1190,c_1169,c_1166,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:43:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.97/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.97/1.99  
% 11.97/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.97/1.99  
% 11.97/1.99  ------  iProver source info
% 11.97/1.99  
% 11.97/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.97/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.97/1.99  git: non_committed_changes: false
% 11.97/1.99  git: last_make_outside_of_git: false
% 11.97/1.99  
% 11.97/1.99  ------ 
% 11.97/1.99  
% 11.97/1.99  ------ Input Options
% 11.97/1.99  
% 11.97/1.99  --out_options                           all
% 11.97/1.99  --tptp_safe_out                         true
% 11.97/1.99  --problem_path                          ""
% 11.97/1.99  --include_path                          ""
% 11.97/1.99  --clausifier                            res/vclausify_rel
% 11.97/1.99  --clausifier_options                    --mode clausify
% 11.97/1.99  --stdin                                 false
% 11.97/1.99  --stats_out                             all
% 11.97/1.99  
% 11.97/1.99  ------ General Options
% 11.97/1.99  
% 11.97/1.99  --fof                                   false
% 11.97/1.99  --time_out_real                         305.
% 11.97/1.99  --time_out_virtual                      -1.
% 11.97/1.99  --symbol_type_check                     false
% 11.97/1.99  --clausify_out                          false
% 11.97/1.99  --sig_cnt_out                           false
% 11.97/1.99  --trig_cnt_out                          false
% 11.97/1.99  --trig_cnt_out_tolerance                1.
% 11.97/1.99  --trig_cnt_out_sk_spl                   false
% 11.97/1.99  --abstr_cl_out                          false
% 11.97/1.99  
% 11.97/1.99  ------ Global Options
% 11.97/1.99  
% 11.97/1.99  --schedule                              default
% 11.97/1.99  --add_important_lit                     false
% 11.97/1.99  --prop_solver_per_cl                    1000
% 11.97/1.99  --min_unsat_core                        false
% 11.97/1.99  --soft_assumptions                      false
% 11.97/1.99  --soft_lemma_size                       3
% 11.97/1.99  --prop_impl_unit_size                   0
% 11.97/1.99  --prop_impl_unit                        []
% 11.97/1.99  --share_sel_clauses                     true
% 11.97/1.99  --reset_solvers                         false
% 11.97/1.99  --bc_imp_inh                            [conj_cone]
% 11.97/1.99  --conj_cone_tolerance                   3.
% 11.97/1.99  --extra_neg_conj                        none
% 11.97/1.99  --large_theory_mode                     true
% 11.97/1.99  --prolific_symb_bound                   200
% 11.97/1.99  --lt_threshold                          2000
% 11.97/1.99  --clause_weak_htbl                      true
% 11.97/1.99  --gc_record_bc_elim                     false
% 11.97/1.99  
% 11.97/1.99  ------ Preprocessing Options
% 11.97/1.99  
% 11.97/1.99  --preprocessing_flag                    true
% 11.97/1.99  --time_out_prep_mult                    0.1
% 11.97/1.99  --splitting_mode                        input
% 11.97/1.99  --splitting_grd                         true
% 11.97/1.99  --splitting_cvd                         false
% 11.97/1.99  --splitting_cvd_svl                     false
% 11.97/1.99  --splitting_nvd                         32
% 11.97/1.99  --sub_typing                            true
% 11.97/1.99  --prep_gs_sim                           true
% 11.97/1.99  --prep_unflatten                        true
% 11.97/1.99  --prep_res_sim                          true
% 11.97/1.99  --prep_upred                            true
% 11.97/1.99  --prep_sem_filter                       exhaustive
% 11.97/1.99  --prep_sem_filter_out                   false
% 11.97/1.99  --pred_elim                             true
% 11.97/1.99  --res_sim_input                         true
% 11.97/1.99  --eq_ax_congr_red                       true
% 11.97/1.99  --pure_diseq_elim                       true
% 11.97/1.99  --brand_transform                       false
% 11.97/1.99  --non_eq_to_eq                          false
% 11.97/1.99  --prep_def_merge                        true
% 11.97/1.99  --prep_def_merge_prop_impl              false
% 11.97/1.99  --prep_def_merge_mbd                    true
% 11.97/1.99  --prep_def_merge_tr_red                 false
% 11.97/1.99  --prep_def_merge_tr_cl                  false
% 11.97/1.99  --smt_preprocessing                     true
% 11.97/1.99  --smt_ac_axioms                         fast
% 11.97/1.99  --preprocessed_out                      false
% 11.97/1.99  --preprocessed_stats                    false
% 11.97/1.99  
% 11.97/1.99  ------ Abstraction refinement Options
% 11.97/1.99  
% 11.97/1.99  --abstr_ref                             []
% 11.97/1.99  --abstr_ref_prep                        false
% 11.97/1.99  --abstr_ref_until_sat                   false
% 11.97/1.99  --abstr_ref_sig_restrict                funpre
% 11.97/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.97/1.99  --abstr_ref_under                       []
% 11.97/1.99  
% 11.97/1.99  ------ SAT Options
% 11.97/1.99  
% 11.97/1.99  --sat_mode                              false
% 11.97/1.99  --sat_fm_restart_options                ""
% 11.97/1.99  --sat_gr_def                            false
% 11.97/1.99  --sat_epr_types                         true
% 11.97/1.99  --sat_non_cyclic_types                  false
% 11.97/1.99  --sat_finite_models                     false
% 11.97/1.99  --sat_fm_lemmas                         false
% 11.97/1.99  --sat_fm_prep                           false
% 11.97/1.99  --sat_fm_uc_incr                        true
% 11.97/1.99  --sat_out_model                         small
% 11.97/1.99  --sat_out_clauses                       false
% 11.97/1.99  
% 11.97/1.99  ------ QBF Options
% 11.97/1.99  
% 11.97/1.99  --qbf_mode                              false
% 11.97/1.99  --qbf_elim_univ                         false
% 11.97/1.99  --qbf_dom_inst                          none
% 11.97/1.99  --qbf_dom_pre_inst                      false
% 11.97/1.99  --qbf_sk_in                             false
% 11.97/1.99  --qbf_pred_elim                         true
% 11.97/1.99  --qbf_split                             512
% 11.97/1.99  
% 11.97/1.99  ------ BMC1 Options
% 11.97/1.99  
% 11.97/1.99  --bmc1_incremental                      false
% 11.97/1.99  --bmc1_axioms                           reachable_all
% 11.97/1.99  --bmc1_min_bound                        0
% 11.97/1.99  --bmc1_max_bound                        -1
% 11.97/1.99  --bmc1_max_bound_default                -1
% 11.97/1.99  --bmc1_symbol_reachability              true
% 11.97/1.99  --bmc1_property_lemmas                  false
% 11.97/1.99  --bmc1_k_induction                      false
% 11.97/1.99  --bmc1_non_equiv_states                 false
% 11.97/1.99  --bmc1_deadlock                         false
% 11.97/1.99  --bmc1_ucm                              false
% 11.97/1.99  --bmc1_add_unsat_core                   none
% 11.97/1.99  --bmc1_unsat_core_children              false
% 11.97/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.97/1.99  --bmc1_out_stat                         full
% 11.97/1.99  --bmc1_ground_init                      false
% 11.97/1.99  --bmc1_pre_inst_next_state              false
% 11.97/1.99  --bmc1_pre_inst_state                   false
% 11.97/1.99  --bmc1_pre_inst_reach_state             false
% 11.97/1.99  --bmc1_out_unsat_core                   false
% 11.97/1.99  --bmc1_aig_witness_out                  false
% 11.97/1.99  --bmc1_verbose                          false
% 11.97/1.99  --bmc1_dump_clauses_tptp                false
% 11.97/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.97/1.99  --bmc1_dump_file                        -
% 11.97/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.97/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.97/1.99  --bmc1_ucm_extend_mode                  1
% 11.97/1.99  --bmc1_ucm_init_mode                    2
% 11.97/1.99  --bmc1_ucm_cone_mode                    none
% 11.97/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.97/1.99  --bmc1_ucm_relax_model                  4
% 11.97/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.97/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.97/1.99  --bmc1_ucm_layered_model                none
% 11.97/1.99  --bmc1_ucm_max_lemma_size               10
% 11.97/1.99  
% 11.97/1.99  ------ AIG Options
% 11.97/1.99  
% 11.97/1.99  --aig_mode                              false
% 11.97/1.99  
% 11.97/1.99  ------ Instantiation Options
% 11.97/1.99  
% 11.97/1.99  --instantiation_flag                    true
% 11.97/1.99  --inst_sos_flag                         false
% 11.97/1.99  --inst_sos_phase                        true
% 11.97/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.97/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.97/1.99  --inst_lit_sel_side                     num_symb
% 11.97/1.99  --inst_solver_per_active                1400
% 11.97/1.99  --inst_solver_calls_frac                1.
% 11.97/1.99  --inst_passive_queue_type               priority_queues
% 11.97/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.97/1.99  --inst_passive_queues_freq              [25;2]
% 11.97/1.99  --inst_dismatching                      true
% 11.97/1.99  --inst_eager_unprocessed_to_passive     true
% 11.97/1.99  --inst_prop_sim_given                   true
% 11.97/1.99  --inst_prop_sim_new                     false
% 11.97/1.99  --inst_subs_new                         false
% 11.97/1.99  --inst_eq_res_simp                      false
% 11.97/1.99  --inst_subs_given                       false
% 11.97/1.99  --inst_orphan_elimination               true
% 11.97/1.99  --inst_learning_loop_flag               true
% 11.97/1.99  --inst_learning_start                   3000
% 11.97/1.99  --inst_learning_factor                  2
% 11.97/1.99  --inst_start_prop_sim_after_learn       3
% 11.97/1.99  --inst_sel_renew                        solver
% 11.97/1.99  --inst_lit_activity_flag                true
% 11.97/1.99  --inst_restr_to_given                   false
% 11.97/1.99  --inst_activity_threshold               500
% 11.97/1.99  --inst_out_proof                        true
% 11.97/1.99  
% 11.97/1.99  ------ Resolution Options
% 11.97/1.99  
% 11.97/1.99  --resolution_flag                       true
% 11.97/1.99  --res_lit_sel                           adaptive
% 11.97/1.99  --res_lit_sel_side                      none
% 11.97/1.99  --res_ordering                          kbo
% 11.97/1.99  --res_to_prop_solver                    active
% 11.97/1.99  --res_prop_simpl_new                    false
% 11.97/1.99  --res_prop_simpl_given                  true
% 11.97/1.99  --res_passive_queue_type                priority_queues
% 11.97/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.97/1.99  --res_passive_queues_freq               [15;5]
% 11.97/1.99  --res_forward_subs                      full
% 11.97/1.99  --res_backward_subs                     full
% 11.97/1.99  --res_forward_subs_resolution           true
% 11.97/1.99  --res_backward_subs_resolution          true
% 11.97/1.99  --res_orphan_elimination                true
% 11.97/1.99  --res_time_limit                        2.
% 11.97/1.99  --res_out_proof                         true
% 11.97/1.99  
% 11.97/1.99  ------ Superposition Options
% 11.97/1.99  
% 11.97/1.99  --superposition_flag                    true
% 11.97/1.99  --sup_passive_queue_type                priority_queues
% 11.97/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.97/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.97/1.99  --demod_completeness_check              fast
% 11.97/1.99  --demod_use_ground                      true
% 11.97/1.99  --sup_to_prop_solver                    passive
% 11.97/1.99  --sup_prop_simpl_new                    true
% 11.97/1.99  --sup_prop_simpl_given                  true
% 11.97/1.99  --sup_fun_splitting                     false
% 11.97/1.99  --sup_smt_interval                      50000
% 11.97/1.99  
% 11.97/1.99  ------ Superposition Simplification Setup
% 11.97/1.99  
% 11.97/1.99  --sup_indices_passive                   []
% 11.97/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.97/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.97/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.97/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.97/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.97/1.99  --sup_full_bw                           [BwDemod]
% 11.97/1.99  --sup_immed_triv                        [TrivRules]
% 11.97/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.97/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.97/1.99  --sup_immed_bw_main                     []
% 11.97/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.97/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.97/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.97/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.97/1.99  
% 11.97/1.99  ------ Combination Options
% 11.97/1.99  
% 11.97/1.99  --comb_res_mult                         3
% 11.97/1.99  --comb_sup_mult                         2
% 11.97/1.99  --comb_inst_mult                        10
% 11.97/1.99  
% 11.97/1.99  ------ Debug Options
% 11.97/1.99  
% 11.97/1.99  --dbg_backtrace                         false
% 11.97/1.99  --dbg_dump_prop_clauses                 false
% 11.97/1.99  --dbg_dump_prop_clauses_file            -
% 11.97/1.99  --dbg_out_stat                          false
% 11.97/1.99  ------ Parsing...
% 11.97/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.97/1.99  
% 11.97/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.97/1.99  
% 11.97/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.97/1.99  
% 11.97/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.97/1.99  ------ Proving...
% 11.97/1.99  ------ Problem Properties 
% 11.97/1.99  
% 11.97/1.99  
% 11.97/1.99  clauses                                 23
% 11.97/1.99  conjectures                             2
% 11.97/1.99  EPR                                     2
% 11.97/1.99  Horn                                    15
% 11.97/1.99  unary                                   4
% 11.97/1.99  binary                                  10
% 11.97/1.99  lits                                    53
% 11.97/1.99  lits eq                                 15
% 11.97/1.99  fd_pure                                 0
% 11.97/1.99  fd_pseudo                               0
% 11.97/1.99  fd_cond                                 1
% 11.97/1.99  fd_pseudo_cond                          7
% 11.97/1.99  AC symbols                              0
% 11.97/1.99  
% 11.97/1.99  ------ Schedule dynamic 5 is on 
% 11.97/1.99  
% 11.97/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.97/1.99  
% 11.97/1.99  
% 11.97/1.99  ------ 
% 11.97/1.99  Current options:
% 11.97/1.99  ------ 
% 11.97/1.99  
% 11.97/1.99  ------ Input Options
% 11.97/1.99  
% 11.97/1.99  --out_options                           all
% 11.97/1.99  --tptp_safe_out                         true
% 11.97/1.99  --problem_path                          ""
% 11.97/1.99  --include_path                          ""
% 11.97/1.99  --clausifier                            res/vclausify_rel
% 11.97/1.99  --clausifier_options                    --mode clausify
% 11.97/1.99  --stdin                                 false
% 11.97/1.99  --stats_out                             all
% 11.97/1.99  
% 11.97/1.99  ------ General Options
% 11.97/1.99  
% 11.97/1.99  --fof                                   false
% 11.97/1.99  --time_out_real                         305.
% 11.97/1.99  --time_out_virtual                      -1.
% 11.97/1.99  --symbol_type_check                     false
% 11.97/1.99  --clausify_out                          false
% 11.97/1.99  --sig_cnt_out                           false
% 11.97/1.99  --trig_cnt_out                          false
% 11.97/1.99  --trig_cnt_out_tolerance                1.
% 11.97/1.99  --trig_cnt_out_sk_spl                   false
% 11.97/1.99  --abstr_cl_out                          false
% 11.97/1.99  
% 11.97/1.99  ------ Global Options
% 11.97/1.99  
% 11.97/1.99  --schedule                              default
% 11.97/1.99  --add_important_lit                     false
% 11.97/1.99  --prop_solver_per_cl                    1000
% 11.97/1.99  --min_unsat_core                        false
% 11.97/1.99  --soft_assumptions                      false
% 11.97/1.99  --soft_lemma_size                       3
% 11.97/1.99  --prop_impl_unit_size                   0
% 11.97/1.99  --prop_impl_unit                        []
% 11.97/1.99  --share_sel_clauses                     true
% 11.97/1.99  --reset_solvers                         false
% 11.97/1.99  --bc_imp_inh                            [conj_cone]
% 11.97/1.99  --conj_cone_tolerance                   3.
% 11.97/1.99  --extra_neg_conj                        none
% 11.97/1.99  --large_theory_mode                     true
% 11.97/1.99  --prolific_symb_bound                   200
% 11.97/1.99  --lt_threshold                          2000
% 11.97/1.99  --clause_weak_htbl                      true
% 11.97/1.99  --gc_record_bc_elim                     false
% 11.97/1.99  
% 11.97/1.99  ------ Preprocessing Options
% 11.97/1.99  
% 11.97/1.99  --preprocessing_flag                    true
% 11.97/1.99  --time_out_prep_mult                    0.1
% 11.97/1.99  --splitting_mode                        input
% 11.97/1.99  --splitting_grd                         true
% 11.97/1.99  --splitting_cvd                         false
% 11.97/1.99  --splitting_cvd_svl                     false
% 11.97/1.99  --splitting_nvd                         32
% 11.97/1.99  --sub_typing                            true
% 11.97/1.99  --prep_gs_sim                           true
% 11.97/1.99  --prep_unflatten                        true
% 11.97/1.99  --prep_res_sim                          true
% 11.97/1.99  --prep_upred                            true
% 11.97/1.99  --prep_sem_filter                       exhaustive
% 11.97/1.99  --prep_sem_filter_out                   false
% 11.97/1.99  --pred_elim                             true
% 11.97/1.99  --res_sim_input                         true
% 11.97/1.99  --eq_ax_congr_red                       true
% 11.97/1.99  --pure_diseq_elim                       true
% 11.97/1.99  --brand_transform                       false
% 11.97/1.99  --non_eq_to_eq                          false
% 11.97/1.99  --prep_def_merge                        true
% 11.97/1.99  --prep_def_merge_prop_impl              false
% 11.97/1.99  --prep_def_merge_mbd                    true
% 11.97/1.99  --prep_def_merge_tr_red                 false
% 11.97/1.99  --prep_def_merge_tr_cl                  false
% 11.97/1.99  --smt_preprocessing                     true
% 11.97/1.99  --smt_ac_axioms                         fast
% 11.97/1.99  --preprocessed_out                      false
% 11.97/1.99  --preprocessed_stats                    false
% 11.97/1.99  
% 11.97/1.99  ------ Abstraction refinement Options
% 11.97/1.99  
% 11.97/1.99  --abstr_ref                             []
% 11.97/1.99  --abstr_ref_prep                        false
% 11.97/1.99  --abstr_ref_until_sat                   false
% 11.97/1.99  --abstr_ref_sig_restrict                funpre
% 11.97/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.97/1.99  --abstr_ref_under                       []
% 11.97/1.99  
% 11.97/1.99  ------ SAT Options
% 11.97/1.99  
% 11.97/1.99  --sat_mode                              false
% 11.97/1.99  --sat_fm_restart_options                ""
% 11.97/1.99  --sat_gr_def                            false
% 11.97/1.99  --sat_epr_types                         true
% 11.97/1.99  --sat_non_cyclic_types                  false
% 11.97/1.99  --sat_finite_models                     false
% 11.97/1.99  --sat_fm_lemmas                         false
% 11.97/1.99  --sat_fm_prep                           false
% 11.97/1.99  --sat_fm_uc_incr                        true
% 11.97/1.99  --sat_out_model                         small
% 11.97/1.99  --sat_out_clauses                       false
% 11.97/1.99  
% 11.97/1.99  ------ QBF Options
% 11.97/1.99  
% 11.97/1.99  --qbf_mode                              false
% 11.97/1.99  --qbf_elim_univ                         false
% 11.97/1.99  --qbf_dom_inst                          none
% 11.97/1.99  --qbf_dom_pre_inst                      false
% 11.97/1.99  --qbf_sk_in                             false
% 11.97/1.99  --qbf_pred_elim                         true
% 11.97/1.99  --qbf_split                             512
% 11.97/1.99  
% 11.97/1.99  ------ BMC1 Options
% 11.97/1.99  
% 11.97/1.99  --bmc1_incremental                      false
% 11.97/1.99  --bmc1_axioms                           reachable_all
% 11.97/1.99  --bmc1_min_bound                        0
% 11.97/1.99  --bmc1_max_bound                        -1
% 11.97/1.99  --bmc1_max_bound_default                -1
% 11.97/1.99  --bmc1_symbol_reachability              true
% 11.97/1.99  --bmc1_property_lemmas                  false
% 11.97/1.99  --bmc1_k_induction                      false
% 11.97/1.99  --bmc1_non_equiv_states                 false
% 11.97/1.99  --bmc1_deadlock                         false
% 11.97/1.99  --bmc1_ucm                              false
% 11.97/1.99  --bmc1_add_unsat_core                   none
% 11.97/1.99  --bmc1_unsat_core_children              false
% 11.97/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.97/1.99  --bmc1_out_stat                         full
% 11.97/1.99  --bmc1_ground_init                      false
% 11.97/1.99  --bmc1_pre_inst_next_state              false
% 11.97/1.99  --bmc1_pre_inst_state                   false
% 11.97/1.99  --bmc1_pre_inst_reach_state             false
% 11.97/1.99  --bmc1_out_unsat_core                   false
% 11.97/1.99  --bmc1_aig_witness_out                  false
% 11.97/1.99  --bmc1_verbose                          false
% 11.97/1.99  --bmc1_dump_clauses_tptp                false
% 11.97/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.97/1.99  --bmc1_dump_file                        -
% 11.97/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.97/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.97/1.99  --bmc1_ucm_extend_mode                  1
% 11.97/1.99  --bmc1_ucm_init_mode                    2
% 11.97/1.99  --bmc1_ucm_cone_mode                    none
% 11.97/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.97/1.99  --bmc1_ucm_relax_model                  4
% 11.97/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.97/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.97/1.99  --bmc1_ucm_layered_model                none
% 11.97/1.99  --bmc1_ucm_max_lemma_size               10
% 11.97/1.99  
% 11.97/1.99  ------ AIG Options
% 11.97/1.99  
% 11.97/1.99  --aig_mode                              false
% 11.97/1.99  
% 11.97/1.99  ------ Instantiation Options
% 11.97/1.99  
% 11.97/1.99  --instantiation_flag                    true
% 11.97/1.99  --inst_sos_flag                         false
% 11.97/1.99  --inst_sos_phase                        true
% 11.97/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.97/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.97/1.99  --inst_lit_sel_side                     none
% 11.97/1.99  --inst_solver_per_active                1400
% 11.97/1.99  --inst_solver_calls_frac                1.
% 11.97/1.99  --inst_passive_queue_type               priority_queues
% 11.97/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.97/1.99  --inst_passive_queues_freq              [25;2]
% 11.97/1.99  --inst_dismatching                      true
% 11.97/1.99  --inst_eager_unprocessed_to_passive     true
% 11.97/1.99  --inst_prop_sim_given                   true
% 11.97/1.99  --inst_prop_sim_new                     false
% 11.97/1.99  --inst_subs_new                         false
% 11.97/1.99  --inst_eq_res_simp                      false
% 11.97/1.99  --inst_subs_given                       false
% 11.97/1.99  --inst_orphan_elimination               true
% 11.97/1.99  --inst_learning_loop_flag               true
% 11.97/1.99  --inst_learning_start                   3000
% 11.97/1.99  --inst_learning_factor                  2
% 11.97/1.99  --inst_start_prop_sim_after_learn       3
% 11.97/1.99  --inst_sel_renew                        solver
% 11.97/1.99  --inst_lit_activity_flag                true
% 11.97/1.99  --inst_restr_to_given                   false
% 11.97/1.99  --inst_activity_threshold               500
% 11.97/1.99  --inst_out_proof                        true
% 11.97/1.99  
% 11.97/1.99  ------ Resolution Options
% 11.97/1.99  
% 11.97/1.99  --resolution_flag                       false
% 11.97/1.99  --res_lit_sel                           adaptive
% 11.97/1.99  --res_lit_sel_side                      none
% 11.97/1.99  --res_ordering                          kbo
% 11.97/1.99  --res_to_prop_solver                    active
% 11.97/1.99  --res_prop_simpl_new                    false
% 11.97/1.99  --res_prop_simpl_given                  true
% 11.97/1.99  --res_passive_queue_type                priority_queues
% 11.97/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.97/1.99  --res_passive_queues_freq               [15;5]
% 11.97/1.99  --res_forward_subs                      full
% 11.97/1.99  --res_backward_subs                     full
% 11.97/1.99  --res_forward_subs_resolution           true
% 11.97/1.99  --res_backward_subs_resolution          true
% 11.97/1.99  --res_orphan_elimination                true
% 11.97/1.99  --res_time_limit                        2.
% 11.97/1.99  --res_out_proof                         true
% 11.97/1.99  
% 11.97/1.99  ------ Superposition Options
% 11.97/1.99  
% 11.97/1.99  --superposition_flag                    true
% 11.97/1.99  --sup_passive_queue_type                priority_queues
% 11.97/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.97/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.97/1.99  --demod_completeness_check              fast
% 11.97/1.99  --demod_use_ground                      true
% 11.97/1.99  --sup_to_prop_solver                    passive
% 11.97/1.99  --sup_prop_simpl_new                    true
% 11.97/1.99  --sup_prop_simpl_given                  true
% 11.97/1.99  --sup_fun_splitting                     false
% 11.97/1.99  --sup_smt_interval                      50000
% 11.97/1.99  
% 11.97/1.99  ------ Superposition Simplification Setup
% 11.97/1.99  
% 11.97/1.99  --sup_indices_passive                   []
% 11.97/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.97/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.97/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.97/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.97/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.97/1.99  --sup_full_bw                           [BwDemod]
% 11.97/1.99  --sup_immed_triv                        [TrivRules]
% 11.97/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.97/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.97/1.99  --sup_immed_bw_main                     []
% 11.97/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.97/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.97/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.97/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.97/1.99  
% 11.97/1.99  ------ Combination Options
% 11.97/1.99  
% 11.97/1.99  --comb_res_mult                         3
% 11.97/1.99  --comb_sup_mult                         2
% 11.97/1.99  --comb_inst_mult                        10
% 11.97/1.99  
% 11.97/1.99  ------ Debug Options
% 11.97/1.99  
% 11.97/1.99  --dbg_backtrace                         false
% 11.97/1.99  --dbg_dump_prop_clauses                 false
% 11.97/1.99  --dbg_dump_prop_clauses_file            -
% 11.97/1.99  --dbg_out_stat                          false
% 11.97/1.99  
% 11.97/1.99  
% 11.97/1.99  
% 11.97/1.99  
% 11.97/1.99  ------ Proving...
% 11.97/1.99  
% 11.97/1.99  
% 11.97/1.99  % SZS status Theorem for theBenchmark.p
% 11.97/1.99  
% 11.97/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.97/1.99  
% 11.97/1.99  fof(f3,axiom,(
% 11.97/1.99    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 11.97/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.97/1.99  
% 11.97/1.99  fof(f25,plain,(
% 11.97/1.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.97/1.99    inference(nnf_transformation,[],[f3])).
% 11.97/1.99  
% 11.97/1.99  fof(f26,plain,(
% 11.97/1.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.97/1.99    inference(flattening,[],[f25])).
% 11.97/1.99  
% 11.97/1.99  fof(f27,plain,(
% 11.97/1.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.97/1.99    inference(rectify,[],[f26])).
% 11.97/1.99  
% 11.97/1.99  fof(f28,plain,(
% 11.97/1.99    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 11.97/1.99    introduced(choice_axiom,[])).
% 11.97/1.99  
% 11.97/1.99  fof(f29,plain,(
% 11.97/1.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.97/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).
% 11.97/1.99  
% 11.97/1.99  fof(f48,plain,(
% 11.97/1.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 11.97/1.99    inference(cnf_transformation,[],[f29])).
% 11.97/1.99  
% 11.97/1.99  fof(f49,plain,(
% 11.97/1.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 11.97/1.99    inference(cnf_transformation,[],[f29])).
% 11.97/1.99  
% 11.97/1.99  fof(f1,axiom,(
% 11.97/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.97/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.97/1.99  
% 11.97/1.99  fof(f38,plain,(
% 11.97/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.97/1.99    inference(cnf_transformation,[],[f1])).
% 11.97/1.99  
% 11.97/1.99  fof(f9,axiom,(
% 11.97/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.97/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.97/1.99  
% 11.97/1.99  fof(f58,plain,(
% 11.97/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.97/1.99    inference(cnf_transformation,[],[f9])).
% 11.97/1.99  
% 11.97/1.99  fof(f71,plain,(
% 11.97/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 11.97/1.99    inference(definition_unfolding,[],[f38,f58,f58])).
% 11.97/1.99  
% 11.97/1.99  fof(f8,axiom,(
% 11.97/1.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 11.97/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.97/1.99  
% 11.97/1.99  fof(f57,plain,(
% 11.97/1.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 11.97/1.99    inference(cnf_transformation,[],[f8])).
% 11.97/1.99  
% 11.97/1.99  fof(f7,axiom,(
% 11.97/1.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 11.97/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.97/1.99  
% 11.97/1.99  fof(f18,plain,(
% 11.97/1.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 11.97/1.99    inference(ennf_transformation,[],[f7])).
% 11.97/1.99  
% 11.97/1.99  fof(f56,plain,(
% 11.97/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 11.97/1.99    inference(cnf_transformation,[],[f18])).
% 11.97/1.99  
% 11.97/1.99  fof(f78,plain,(
% 11.97/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 11.97/1.99    inference(definition_unfolding,[],[f56,f58])).
% 11.97/1.99  
% 11.97/1.99  fof(f46,plain,(
% 11.97/1.99    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 11.97/1.99    inference(cnf_transformation,[],[f29])).
% 11.97/1.99  
% 11.97/1.99  fof(f87,plain,(
% 11.97/1.99    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 11.97/1.99    inference(equality_resolution,[],[f46])).
% 11.97/1.99  
% 11.97/1.99  fof(f45,plain,(
% 11.97/1.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 11.97/1.99    inference(cnf_transformation,[],[f29])).
% 11.97/1.99  
% 11.97/1.99  fof(f88,plain,(
% 11.97/1.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 11.97/1.99    inference(equality_resolution,[],[f45])).
% 11.97/1.99  
% 11.97/1.99  fof(f5,axiom,(
% 11.97/1.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.97/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.97/1.99  
% 11.97/1.99  fof(f32,plain,(
% 11.97/1.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.97/1.99    inference(nnf_transformation,[],[f5])).
% 11.97/1.99  
% 11.97/1.99  fof(f33,plain,(
% 11.97/1.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.97/1.99    inference(flattening,[],[f32])).
% 11.97/1.99  
% 11.97/1.99  fof(f53,plain,(
% 11.97/1.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 11.97/1.99    inference(cnf_transformation,[],[f33])).
% 11.97/1.99  
% 11.97/1.99  fof(f89,plain,(
% 11.97/1.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.97/1.99    inference(equality_resolution,[],[f53])).
% 11.97/1.99  
% 11.97/1.99  fof(f14,axiom,(
% 11.97/1.99    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 11.97/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.97/1.99  
% 11.97/1.99  fof(f34,plain,(
% 11.97/1.99    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 11.97/1.99    inference(nnf_transformation,[],[f14])).
% 11.97/1.99  
% 11.97/1.99  fof(f64,plain,(
% 11.97/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 11.97/1.99    inference(cnf_transformation,[],[f34])).
% 11.97/1.99  
% 11.97/1.99  fof(f10,axiom,(
% 11.97/1.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 11.97/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.97/1.99  
% 11.97/1.99  fof(f59,plain,(
% 11.97/1.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 11.97/1.99    inference(cnf_transformation,[],[f10])).
% 11.97/1.99  
% 11.97/1.99  fof(f11,axiom,(
% 11.97/1.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 11.97/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.97/1.99  
% 11.97/1.99  fof(f60,plain,(
% 11.97/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 11.97/1.99    inference(cnf_transformation,[],[f11])).
% 11.97/1.99  
% 11.97/1.99  fof(f12,axiom,(
% 11.97/1.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.97/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.97/1.99  
% 11.97/1.99  fof(f61,plain,(
% 11.97/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.97/1.99    inference(cnf_transformation,[],[f12])).
% 11.97/1.99  
% 11.97/1.99  fof(f13,axiom,(
% 11.97/1.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 11.97/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.97/1.99  
% 11.97/1.99  fof(f62,plain,(
% 11.97/1.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 11.97/1.99    inference(cnf_transformation,[],[f13])).
% 11.97/1.99  
% 11.97/1.99  fof(f67,plain,(
% 11.97/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 11.97/1.99    inference(definition_unfolding,[],[f61,f62])).
% 11.97/1.99  
% 11.97/1.99  fof(f68,plain,(
% 11.97/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 11.97/1.99    inference(definition_unfolding,[],[f60,f67])).
% 11.97/1.99  
% 11.97/1.99  fof(f69,plain,(
% 11.97/1.99    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 11.97/1.99    inference(definition_unfolding,[],[f59,f68])).
% 11.97/1.99  
% 11.97/1.99  fof(f79,plain,(
% 11.97/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 11.97/1.99    inference(definition_unfolding,[],[f64,f69])).
% 11.97/1.99  
% 11.97/1.99  fof(f15,conjecture,(
% 11.97/1.99    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) <=> ~r2_hidden(X0,X1))),
% 11.97/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.97/1.99  
% 11.97/1.99  fof(f16,negated_conjecture,(
% 11.97/1.99    ~! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) <=> ~r2_hidden(X0,X1))),
% 11.97/1.99    inference(negated_conjecture,[],[f15])).
% 11.97/1.99  
% 11.97/1.99  fof(f19,plain,(
% 11.97/1.99    ? [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) <~> ~r2_hidden(X0,X1))),
% 11.97/1.99    inference(ennf_transformation,[],[f16])).
% 11.97/1.99  
% 11.97/1.99  fof(f35,plain,(
% 11.97/1.99    ? [X0,X1] : ((r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)) & (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)))),
% 11.97/1.99    inference(nnf_transformation,[],[f19])).
% 11.97/1.99  
% 11.97/1.99  fof(f36,plain,(
% 11.97/1.99    ? [X0,X1] : ((r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)) & (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0))) => ((r2_hidden(sK3,sK4) | k4_xboole_0(k1_tarski(sK3),sK4) != k1_tarski(sK3)) & (~r2_hidden(sK3,sK4) | k4_xboole_0(k1_tarski(sK3),sK4) = k1_tarski(sK3)))),
% 11.97/1.99    introduced(choice_axiom,[])).
% 11.97/1.99  
% 11.97/1.99  fof(f37,plain,(
% 11.97/1.99    (r2_hidden(sK3,sK4) | k4_xboole_0(k1_tarski(sK3),sK4) != k1_tarski(sK3)) & (~r2_hidden(sK3,sK4) | k4_xboole_0(k1_tarski(sK3),sK4) = k1_tarski(sK3))),
% 11.97/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f35,f36])).
% 11.97/1.99  
% 11.97/1.99  fof(f65,plain,(
% 11.97/1.99    ~r2_hidden(sK3,sK4) | k4_xboole_0(k1_tarski(sK3),sK4) = k1_tarski(sK3)),
% 11.97/1.99    inference(cnf_transformation,[],[f37])).
% 11.97/1.99  
% 11.97/1.99  fof(f82,plain,(
% 11.97/1.99    ~r2_hidden(sK3,sK4) | k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)),
% 11.97/1.99    inference(definition_unfolding,[],[f65,f69,f69])).
% 11.97/1.99  
% 11.97/1.99  fof(f63,plain,(
% 11.97/1.99    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 11.97/1.99    inference(cnf_transformation,[],[f34])).
% 11.97/1.99  
% 11.97/1.99  fof(f80,plain,(
% 11.97/1.99    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) != X0) )),
% 11.97/1.99    inference(definition_unfolding,[],[f63,f69])).
% 11.97/1.99  
% 11.97/1.99  fof(f50,plain,(
% 11.97/1.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 11.97/1.99    inference(cnf_transformation,[],[f29])).
% 11.97/1.99  
% 11.97/1.99  fof(f66,plain,(
% 11.97/1.99    r2_hidden(sK3,sK4) | k4_xboole_0(k1_tarski(sK3),sK4) != k1_tarski(sK3)),
% 11.97/1.99    inference(cnf_transformation,[],[f37])).
% 11.97/1.99  
% 11.97/1.99  fof(f81,plain,(
% 11.97/1.99    r2_hidden(sK3,sK4) | k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4) != k3_enumset1(sK3,sK3,sK3,sK3,sK3)),
% 11.97/1.99    inference(definition_unfolding,[],[f66,f69,f69])).
% 11.97/1.99  
% 11.97/1.99  cnf(c_497,plain,
% 11.97/1.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.97/1.99      theory(equality) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_1272,plain,
% 11.97/1.99      ( r2_hidden(X0,X1)
% 11.97/1.99      | ~ r2_hidden(sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),sK4)
% 11.97/1.99      | X0 != sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
% 11.97/1.99      | X1 != sK4 ),
% 11.97/1.99      inference(instantiation,[status(thm)],[c_497]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_1849,plain,
% 11.97/1.99      ( r2_hidden(X0,k4_xboole_0(X1,X2))
% 11.97/1.99      | ~ r2_hidden(sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),sK4)
% 11.97/1.99      | X0 != sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
% 11.97/1.99      | k4_xboole_0(X1,X2) != sK4 ),
% 11.97/1.99      inference(instantiation,[status(thm)],[c_1272]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_12581,plain,
% 11.97/1.99      ( r2_hidden(sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k4_xboole_0(X0,X1))
% 11.97/1.99      | ~ r2_hidden(sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),sK4)
% 11.97/1.99      | sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
% 11.97/1.99      | k4_xboole_0(X0,X1) != sK4 ),
% 11.97/1.99      inference(instantiation,[status(thm)],[c_1849]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_50552,plain,
% 11.97/1.99      ( r2_hidden(sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k4_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))
% 11.97/1.99      | ~ r2_hidden(sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),sK4)
% 11.97/1.99      | sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
% 11.97/1.99      | k4_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != sK4 ),
% 11.97/1.99      inference(instantiation,[status(thm)],[c_12581]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_10,plain,
% 11.97/1.99      ( r2_hidden(sK1(X0,X1,X2),X0)
% 11.97/1.99      | r2_hidden(sK1(X0,X1,X2),X2)
% 11.97/1.99      | k4_xboole_0(X0,X1) = X2 ),
% 11.97/1.99      inference(cnf_transformation,[],[f48]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_994,plain,
% 11.97/1.99      ( k4_xboole_0(X0,X1) = X2
% 11.97/1.99      | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
% 11.97/1.99      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 11.97/1.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_9,plain,
% 11.97/1.99      ( ~ r2_hidden(sK1(X0,X1,X2),X1)
% 11.97/1.99      | r2_hidden(sK1(X0,X1,X2),X2)
% 11.97/1.99      | k4_xboole_0(X0,X1) = X2 ),
% 11.97/1.99      inference(cnf_transformation,[],[f49]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_995,plain,
% 11.97/1.99      ( k4_xboole_0(X0,X1) = X2
% 11.97/1.99      | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top
% 11.97/1.99      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 11.97/1.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_3735,plain,
% 11.97/1.99      ( k4_xboole_0(X0,X0) = X1
% 11.97/1.99      | r2_hidden(sK1(X0,X0,X1),X1) = iProver_top ),
% 11.97/1.99      inference(superposition,[status(thm)],[c_994,c_995]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_1,plain,
% 11.97/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.97/1.99      inference(cnf_transformation,[],[f71]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_19,plain,
% 11.97/1.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 11.97/1.99      inference(cnf_transformation,[],[f57]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_986,plain,
% 11.97/1.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 11.97/1.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_18,plain,
% 11.97/1.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 11.97/1.99      inference(cnf_transformation,[],[f78]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_987,plain,
% 11.97/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 11.97/1.99      | r1_tarski(X0,X1) != iProver_top ),
% 11.97/1.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_1307,plain,
% 11.97/1.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
% 11.97/1.99      inference(superposition,[status(thm)],[c_986,c_987]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_12,plain,
% 11.97/1.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 11.97/1.99      inference(cnf_transformation,[],[f87]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_992,plain,
% 11.97/1.99      ( r2_hidden(X0,X1) != iProver_top
% 11.97/1.99      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 11.97/1.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_1775,plain,
% 11.97/1.99      ( r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top
% 11.97/1.99      | r2_hidden(X0,k4_xboole_0(k4_xboole_0(X1,X2),X1)) != iProver_top ),
% 11.97/1.99      inference(superposition,[status(thm)],[c_1307,c_992]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_13,plain,
% 11.97/1.99      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 11.97/1.99      inference(cnf_transformation,[],[f88]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_991,plain,
% 11.97/1.99      ( r2_hidden(X0,X1) = iProver_top
% 11.97/1.99      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 11.97/1.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_23109,plain,
% 11.97/1.99      ( r2_hidden(X0,k4_xboole_0(k4_xboole_0(X1,X2),X1)) != iProver_top ),
% 11.97/1.99      inference(forward_subsumption_resolution,
% 11.97/1.99                [status(thm)],
% 11.97/1.99                [c_1775,c_991]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_23133,plain,
% 11.97/1.99      ( r2_hidden(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2)) != iProver_top ),
% 11.97/1.99      inference(superposition,[status(thm)],[c_1,c_23109]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_24255,plain,
% 11.97/1.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k4_xboole_0(X2,X2) ),
% 11.97/1.99      inference(superposition,[status(thm)],[c_3735,c_23133]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_16,plain,
% 11.97/1.99      ( r1_tarski(X0,X0) ),
% 11.97/1.99      inference(cnf_transformation,[],[f89]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_988,plain,
% 11.97/1.99      ( r1_tarski(X0,X0) = iProver_top ),
% 11.97/1.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_1306,plain,
% 11.97/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 11.97/1.99      inference(superposition,[status(thm)],[c_988,c_987]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_24906,plain,
% 11.97/1.99      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2)) = X0 ),
% 11.97/1.99      inference(superposition,[status(thm)],[c_24255,c_1306]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_20,plain,
% 11.97/1.99      ( r2_hidden(X0,X1)
% 11.97/1.99      | k4_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X0)) = X1 ),
% 11.97/1.99      inference(cnf_transformation,[],[f79]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_985,plain,
% 11.97/1.99      ( k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) = X0
% 11.97/1.99      | r2_hidden(X1,X0) = iProver_top ),
% 11.97/1.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_23,negated_conjecture,
% 11.97/1.99      ( ~ r2_hidden(sK3,sK4)
% 11.97/1.99      | k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 11.97/1.99      inference(cnf_transformation,[],[f82]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_982,plain,
% 11.97/1.99      ( k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
% 11.97/1.99      | r2_hidden(sK3,sK4) != iProver_top ),
% 11.97/1.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_2471,plain,
% 11.97/1.99      ( k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
% 11.97/1.99      | k4_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = sK4 ),
% 11.97/1.99      inference(superposition,[status(thm)],[c_985,c_982]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_1774,plain,
% 11.97/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 11.97/1.99      inference(superposition,[status(thm)],[c_1307,c_1]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_2046,plain,
% 11.97/1.99      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 11.97/1.99      inference(superposition,[status(thm)],[c_1,c_1774]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_2562,plain,
% 11.97/1.99      ( k4_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = sK4
% 11.97/1.99      | k4_xboole_0(sK4,k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k4_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
% 11.97/1.99      inference(superposition,[status(thm)],[c_2471,c_2046]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_24957,plain,
% 11.97/1.99      ( k4_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = sK4
% 11.97/1.99      | k4_xboole_0(sK4,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
% 11.97/1.99      inference(superposition,[status(thm)],[c_24255,c_2562]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_26899,plain,
% 11.97/1.99      ( k4_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = sK4 ),
% 11.97/1.99      inference(demodulation,[status(thm)],[c_24906,c_24957]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_493,plain,( X0 = X0 ),theory(equality) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_3163,plain,
% 11.97/1.99      ( sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
% 11.97/1.99      inference(instantiation,[status(thm)],[c_493]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_1247,plain,
% 11.97/1.99      ( ~ r2_hidden(sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3))
% 11.97/1.99      | ~ r2_hidden(sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k4_xboole_0(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
% 11.97/1.99      inference(instantiation,[status(thm)],[c_12]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_1632,plain,
% 11.97/1.99      ( ~ r2_hidden(sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3))
% 11.97/1.99      | ~ r2_hidden(sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k4_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
% 11.97/1.99      inference(instantiation,[status(thm)],[c_1247]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_21,plain,
% 11.97/1.99      ( ~ r2_hidden(X0,X1)
% 11.97/1.99      | k4_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X0)) != X1 ),
% 11.97/1.99      inference(cnf_transformation,[],[f80]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_1190,plain,
% 11.97/1.99      ( ~ r2_hidden(sK3,sK4)
% 11.97/1.99      | k4_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != sK4 ),
% 11.97/1.99      inference(instantiation,[status(thm)],[c_21]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_8,plain,
% 11.97/1.99      ( ~ r2_hidden(sK1(X0,X1,X2),X0)
% 11.97/1.99      | ~ r2_hidden(sK1(X0,X1,X2),X2)
% 11.97/1.99      | r2_hidden(sK1(X0,X1,X2),X1)
% 11.97/1.99      | k4_xboole_0(X0,X1) = X2 ),
% 11.97/1.99      inference(cnf_transformation,[],[f50]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_1169,plain,
% 11.97/1.99      ( ~ r2_hidden(sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3))
% 11.97/1.99      | r2_hidden(sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),sK4)
% 11.97/1.99      | k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 11.97/1.99      inference(instantiation,[status(thm)],[c_8]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_1166,plain,
% 11.97/1.99      ( r2_hidden(sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK3,sK3,sK3,sK3,sK3))
% 11.97/1.99      | k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 11.97/1.99      inference(instantiation,[status(thm)],[c_10]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(c_22,negated_conjecture,
% 11.97/1.99      ( r2_hidden(sK3,sK4)
% 11.97/1.99      | k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4) != k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 11.97/1.99      inference(cnf_transformation,[],[f81]) ).
% 11.97/1.99  
% 11.97/1.99  cnf(contradiction,plain,
% 11.97/1.99      ( $false ),
% 11.97/1.99      inference(minisat,
% 11.97/1.99                [status(thm)],
% 11.97/1.99                [c_50552,c_26899,c_3163,c_1632,c_1190,c_1169,c_1166,c_22]) ).
% 11.97/1.99  
% 11.97/1.99  
% 11.97/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.97/1.99  
% 11.97/1.99  ------                               Statistics
% 11.97/1.99  
% 11.97/1.99  ------ General
% 11.97/1.99  
% 11.97/1.99  abstr_ref_over_cycles:                  0
% 11.97/1.99  abstr_ref_under_cycles:                 0
% 11.97/1.99  gc_basic_clause_elim:                   0
% 11.97/1.99  forced_gc_time:                         0
% 11.97/1.99  parsing_time:                           0.01
% 11.97/1.99  unif_index_cands_time:                  0.
% 11.97/1.99  unif_index_add_time:                    0.
% 11.97/1.99  orderings_time:                         0.
% 11.97/1.99  out_proof_time:                         0.008
% 11.97/1.99  total_time:                             1.303
% 11.97/1.99  num_of_symbols:                         42
% 11.97/1.99  num_of_terms:                           47951
% 11.97/1.99  
% 11.97/1.99  ------ Preprocessing
% 11.97/1.99  
% 11.97/1.99  num_of_splits:                          0
% 11.97/1.99  num_of_split_atoms:                     0
% 11.97/1.99  num_of_reused_defs:                     0
% 11.97/1.99  num_eq_ax_congr_red:                    27
% 11.97/1.99  num_of_sem_filtered_clauses:            1
% 11.97/1.99  num_of_subtypes:                        0
% 11.97/1.99  monotx_restored_types:                  0
% 11.97/1.99  sat_num_of_epr_types:                   0
% 11.97/1.99  sat_num_of_non_cyclic_types:            0
% 11.97/1.99  sat_guarded_non_collapsed_types:        0
% 11.97/1.99  num_pure_diseq_elim:                    0
% 11.97/1.99  simp_replaced_by:                       0
% 11.97/1.99  res_preprocessed:                       107
% 11.97/1.99  prep_upred:                             0
% 11.97/1.99  prep_unflattend:                        0
% 11.97/1.99  smt_new_axioms:                         0
% 11.97/1.99  pred_elim_cands:                        2
% 11.97/1.99  pred_elim:                              0
% 11.97/1.99  pred_elim_cl:                           0
% 11.97/1.99  pred_elim_cycles:                       2
% 11.97/1.99  merged_defs:                            16
% 11.97/1.99  merged_defs_ncl:                        0
% 11.97/1.99  bin_hyper_res:                          16
% 11.97/1.99  prep_cycles:                            4
% 11.97/1.99  pred_elim_time:                         0.
% 11.97/1.99  splitting_time:                         0.
% 11.97/1.99  sem_filter_time:                        0.
% 11.97/1.99  monotx_time:                            0.001
% 11.97/1.99  subtype_inf_time:                       0.
% 11.97/1.99  
% 11.97/1.99  ------ Problem properties
% 11.97/1.99  
% 11.97/1.99  clauses:                                23
% 11.97/1.99  conjectures:                            2
% 11.97/1.99  epr:                                    2
% 11.97/1.99  horn:                                   15
% 11.97/1.99  ground:                                 2
% 11.97/1.99  unary:                                  4
% 11.97/1.99  binary:                                 10
% 11.97/1.99  lits:                                   53
% 11.97/1.99  lits_eq:                                15
% 11.97/1.99  fd_pure:                                0
% 11.97/1.99  fd_pseudo:                              0
% 11.97/1.99  fd_cond:                                1
% 11.97/1.99  fd_pseudo_cond:                         7
% 11.97/1.99  ac_symbols:                             0
% 11.97/1.99  
% 11.97/1.99  ------ Propositional Solver
% 11.97/1.99  
% 11.97/1.99  prop_solver_calls:                      31
% 11.97/1.99  prop_fast_solver_calls:                 1091
% 11.97/1.99  smt_solver_calls:                       0
% 11.97/1.99  smt_fast_solver_calls:                  0
% 11.97/1.99  prop_num_of_clauses:                    11061
% 11.97/1.99  prop_preprocess_simplified:             15115
% 11.97/1.99  prop_fo_subsumed:                       75
% 11.97/1.99  prop_solver_time:                       0.
% 11.97/1.99  smt_solver_time:                        0.
% 11.97/1.99  smt_fast_solver_time:                   0.
% 11.97/1.99  prop_fast_solver_time:                  0.
% 11.97/1.99  prop_unsat_core_time:                   0.
% 11.97/1.99  
% 11.97/1.99  ------ QBF
% 11.97/1.99  
% 11.97/1.99  qbf_q_res:                              0
% 11.97/1.99  qbf_num_tautologies:                    0
% 11.97/1.99  qbf_prep_cycles:                        0
% 11.97/1.99  
% 11.97/1.99  ------ BMC1
% 11.97/1.99  
% 11.97/1.99  bmc1_current_bound:                     -1
% 11.97/1.99  bmc1_last_solved_bound:                 -1
% 11.97/1.99  bmc1_unsat_core_size:                   -1
% 11.97/1.99  bmc1_unsat_core_parents_size:           -1
% 11.97/1.99  bmc1_merge_next_fun:                    0
% 11.97/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.97/1.99  
% 11.97/1.99  ------ Instantiation
% 11.97/1.99  
% 11.97/1.99  inst_num_of_clauses:                    2057
% 11.97/1.99  inst_num_in_passive:                    440
% 11.97/1.99  inst_num_in_active:                     742
% 11.97/1.99  inst_num_in_unprocessed:                874
% 11.97/1.99  inst_num_of_loops:                      946
% 11.97/1.99  inst_num_of_learning_restarts:          0
% 11.97/1.99  inst_num_moves_active_passive:          199
% 11.97/1.99  inst_lit_activity:                      0
% 11.97/1.99  inst_lit_activity_moves:                0
% 11.97/1.99  inst_num_tautologies:                   0
% 11.97/1.99  inst_num_prop_implied:                  0
% 11.97/1.99  inst_num_existing_simplified:           0
% 11.97/1.99  inst_num_eq_res_simplified:             0
% 11.97/1.99  inst_num_child_elim:                    0
% 11.97/1.99  inst_num_of_dismatching_blockings:      4837
% 11.97/1.99  inst_num_of_non_proper_insts:           2942
% 11.97/1.99  inst_num_of_duplicates:                 0
% 11.97/1.99  inst_inst_num_from_inst_to_res:         0
% 11.97/1.99  inst_dismatching_checking_time:         0.
% 11.97/1.99  
% 11.97/1.99  ------ Resolution
% 11.97/1.99  
% 11.97/1.99  res_num_of_clauses:                     0
% 11.97/1.99  res_num_in_passive:                     0
% 11.97/1.99  res_num_in_active:                      0
% 11.97/1.99  res_num_of_loops:                       111
% 11.97/1.99  res_forward_subset_subsumed:            105
% 11.97/1.99  res_backward_subset_subsumed:           0
% 11.97/1.99  res_forward_subsumed:                   0
% 11.97/1.99  res_backward_subsumed:                  0
% 11.97/1.99  res_forward_subsumption_resolution:     0
% 11.97/1.99  res_backward_subsumption_resolution:    0
% 11.97/1.99  res_clause_to_clause_subsumption:       38740
% 11.97/1.99  res_orphan_elimination:                 0
% 11.97/1.99  res_tautology_del:                      193
% 11.97/1.99  res_num_eq_res_simplified:              0
% 11.97/1.99  res_num_sel_changes:                    0
% 11.97/1.99  res_moves_from_active_to_pass:          0
% 11.97/1.99  
% 11.97/1.99  ------ Superposition
% 11.97/1.99  
% 11.97/1.99  sup_time_total:                         0.
% 11.97/1.99  sup_time_generating:                    0.
% 11.97/1.99  sup_time_sim_full:                      0.
% 11.97/1.99  sup_time_sim_immed:                     0.
% 11.97/1.99  
% 11.97/1.99  sup_num_of_clauses:                     1550
% 11.97/1.99  sup_num_in_active:                      98
% 11.97/1.99  sup_num_in_passive:                     1452
% 11.97/1.99  sup_num_of_loops:                       188
% 11.97/1.99  sup_fw_superposition:                   4143
% 11.97/1.99  sup_bw_superposition:                   4723
% 11.97/1.99  sup_immediate_simplified:               5289
% 11.97/1.99  sup_given_eliminated:                   10
% 11.97/1.99  comparisons_done:                       0
% 11.97/1.99  comparisons_avoided:                    98
% 11.97/1.99  
% 11.97/1.99  ------ Simplifications
% 11.97/1.99  
% 11.97/1.99  
% 11.97/1.99  sim_fw_subset_subsumed:                 626
% 11.97/1.99  sim_bw_subset_subsumed:                 331
% 11.97/1.99  sim_fw_subsumed:                        879
% 11.97/1.99  sim_bw_subsumed:                        77
% 11.97/1.99  sim_fw_subsumption_res:                 12
% 11.97/1.99  sim_bw_subsumption_res:                 2
% 11.97/1.99  sim_tautology_del:                      102
% 11.97/1.99  sim_eq_tautology_del:                   565
% 11.97/1.99  sim_eq_res_simp:                        5
% 11.97/1.99  sim_fw_demodulated:                     2954
% 11.97/1.99  sim_bw_demodulated:                     684
% 11.97/1.99  sim_light_normalised:                   2178
% 11.97/1.99  sim_joinable_taut:                      0
% 11.97/1.99  sim_joinable_simp:                      0
% 11.97/1.99  sim_ac_normalised:                      0
% 11.97/1.99  sim_smt_subsumption:                    0
% 11.97/1.99  
%------------------------------------------------------------------------------
