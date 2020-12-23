%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:34:04 EST 2020

% Result     : Theorem 11.62s
% Output     : CNFRefutation 11.62s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 304 expanded)
%              Number of clauses        :   37 (  71 expanded)
%              Number of leaves         :   22 (  85 expanded)
%              Depth                    :   18
%              Number of atoms          :  202 ( 622 expanded)
%              Number of equality atoms :  115 ( 323 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f30])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f20,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f20])).

fof(f24,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f21])).

fof(f33,plain,
    ( ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)
   => k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f24,f33])).

fof(f60,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f54,f61])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f53,f62])).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f52,f63])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f64])).

fof(f66,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f65])).

fof(f76,plain,(
    k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f60,f49,f66])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f9])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

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
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f38,f45])).

fof(f78,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f71])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f43,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f72,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f37,f45])).

fof(f79,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f72])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f75,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f58,f45,f66,f66,f66])).

fof(f80,plain,(
    ! [X1] : k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f75])).

cnf(c_9,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_39134,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_16,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_11,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_101,negated_conjecture,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_16,c_11,c_1])).

cnf(c_39232,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_0,c_101])).

cnf(c_12,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_39254,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_12,c_11])).

cnf(c_10,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_39237,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_10,c_1])).

cnf(c_39554,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_39254,c_39237])).

cnf(c_39565,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k5_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_39232,c_39554])).

cnf(c_39584,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = sK3 ),
    inference(demodulation,[status(thm)],[c_39565,c_10])).

cnf(c_6,negated_conjecture,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_39136,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_39233,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_39136])).

cnf(c_40327,plain,
    ( r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_39584,c_39233])).

cnf(c_40393,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_39134,c_40327])).

cnf(c_47904,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_40393,c_39584])).

cnf(c_39513,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_xboole_0(k1_xboole_0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_39237,c_39136])).

cnf(c_8,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_5080,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5177,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_5080])).

cnf(c_5188,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_5177])).

cnf(c_5231,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_10,c_1])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_5079,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6200,plain,
    ( r2_hidden(X0,k3_xboole_0(k1_xboole_0,X1)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5231,c_5079])).

cnf(c_39641,plain,
    ( r2_hidden(X0,k3_xboole_0(k1_xboole_0,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_39513,c_5188,c_6200])).

cnf(c_39646,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_39134,c_39641])).

cnf(c_47906,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_47904,c_10,c_39646])).

cnf(c_15,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_39174,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_15,c_8,c_12])).

cnf(c_39182,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_39174])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_47906,c_39182])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:29:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.62/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.62/1.99  
% 11.62/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.62/1.99  
% 11.62/1.99  ------  iProver source info
% 11.62/1.99  
% 11.62/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.62/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.62/1.99  git: non_committed_changes: false
% 11.62/1.99  git: last_make_outside_of_git: false
% 11.62/1.99  
% 11.62/1.99  ------ 
% 11.62/1.99  ------ Parsing...
% 11.62/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.62/1.99  
% 11.62/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.62/1.99  
% 11.62/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.62/1.99  
% 11.62/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.62/1.99  ------ Proving...
% 11.62/1.99  ------ Problem Properties 
% 11.62/1.99  
% 11.62/1.99  
% 11.62/1.99  clauses                                 17
% 11.62/1.99  conjectures                             3
% 11.62/1.99  EPR                                     0
% 11.62/1.99  Horn                                    11
% 11.62/1.99  unary                                   9
% 11.62/1.99  binary                                  4
% 11.62/1.99  lits                                    30
% 11.62/1.99  lits eq                                 15
% 11.62/1.99  fd_pure                                 0
% 11.62/1.99  fd_pseudo                               0
% 11.62/1.99  fd_cond                                 1
% 11.62/1.99  fd_pseudo_cond                          4
% 11.62/1.99  AC symbols                              1
% 11.62/1.99  
% 11.62/1.99  ------ Input Options Time Limit: Unbounded
% 11.62/1.99  
% 11.62/1.99  
% 11.62/1.99  
% 11.62/1.99  
% 11.62/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 11.62/1.99  Current options:
% 11.62/1.99  ------ 
% 11.62/1.99  
% 11.62/1.99  
% 11.62/1.99  
% 11.62/1.99  
% 11.62/1.99  ------ Proving...
% 11.62/1.99  
% 11.62/1.99  
% 11.62/1.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.62/1.99  
% 11.62/1.99  ------ Proving...
% 11.62/1.99  
% 11.62/1.99  
% 11.62/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.62/1.99  
% 11.62/1.99  ------ Proving...
% 11.62/1.99  
% 11.62/1.99  
% 11.62/1.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.62/1.99  
% 11.62/1.99  ------ Proving...
% 11.62/1.99  
% 11.62/1.99  
% 11.62/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.62/1.99  
% 11.62/1.99  ------ Proving...
% 11.62/1.99  
% 11.62/1.99  
% 11.62/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.62/1.99  
% 11.62/1.99  ------ Proving...
% 11.62/1.99  
% 11.62/1.99  
% 11.62/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.62/1.99  
% 11.62/1.99  ------ Proving...
% 11.62/1.99  
% 11.62/1.99  
% 11.62/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.62/1.99  
% 11.62/1.99  ------ Proving...
% 11.62/1.99  
% 11.62/1.99  
% 11.62/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.62/1.99  
% 11.62/1.99  ------ Proving...
% 11.62/1.99  
% 11.62/1.99  
% 11.62/1.99  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.62/1.99  
% 11.62/1.99  ------ Proving...
% 11.62/1.99  
% 11.62/1.99  
% 11.62/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.62/1.99  
% 11.62/1.99  ------ Proving...
% 11.62/1.99  
% 11.62/1.99  
% 11.62/1.99  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.62/1.99  
% 11.62/1.99  ------ Proving...
% 11.62/1.99  
% 11.62/1.99  
% 11.62/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.62/1.99  
% 11.62/1.99  ------ Proving...
% 11.62/1.99  
% 11.62/1.99  
% 11.62/1.99  ------ Preprocessing... sf_s  rm: 10 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.62/1.99  
% 11.62/1.99  ------ Proving...
% 11.62/1.99  
% 11.62/1.99  
% 11.62/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.62/1.99  
% 11.62/1.99  ------ Proving...
% 11.62/1.99  
% 11.62/1.99  
% 11.62/1.99  ------ Preprocessing... sf_s  rm: 10 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.62/1.99  
% 11.62/1.99  ------ Proving...
% 11.62/1.99  
% 11.62/1.99  
% 11.62/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.62/1.99  
% 11.62/1.99  ------ Proving...
% 11.62/1.99  
% 11.62/1.99  
% 11.62/1.99  % SZS status Theorem for theBenchmark.p
% 11.62/1.99  
% 11.62/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.62/1.99  
% 11.62/1.99  fof(f5,axiom,(
% 11.62/1.99    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 11.62/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.99  
% 11.62/1.99  fof(f23,plain,(
% 11.62/1.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 11.62/1.99    inference(ennf_transformation,[],[f5])).
% 11.62/1.99  
% 11.62/1.99  fof(f30,plain,(
% 11.62/1.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 11.62/1.99    introduced(choice_axiom,[])).
% 11.62/1.99  
% 11.62/1.99  fof(f31,plain,(
% 11.62/1.99    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 11.62/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f30])).
% 11.62/1.99  
% 11.62/1.99  fof(f44,plain,(
% 11.62/1.99    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 11.62/1.99    inference(cnf_transformation,[],[f31])).
% 11.62/1.99  
% 11.62/1.99  fof(f1,axiom,(
% 11.62/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.62/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.99  
% 11.62/1.99  fof(f35,plain,(
% 11.62/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.62/1.99    inference(cnf_transformation,[],[f1])).
% 11.62/1.99  
% 11.62/1.99  fof(f20,conjecture,(
% 11.62/1.99    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 11.62/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.99  
% 11.62/1.99  fof(f21,negated_conjecture,(
% 11.62/1.99    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 11.62/1.99    inference(negated_conjecture,[],[f20])).
% 11.62/1.99  
% 11.62/1.99  fof(f24,plain,(
% 11.62/1.99    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 11.62/1.99    inference(ennf_transformation,[],[f21])).
% 11.62/1.99  
% 11.62/1.99  fof(f33,plain,(
% 11.62/1.99    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) => k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3)),
% 11.62/1.99    introduced(choice_axiom,[])).
% 11.62/1.99  
% 11.62/1.99  fof(f34,plain,(
% 11.62/1.99    k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3)),
% 11.62/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f24,f33])).
% 11.62/1.99  
% 11.62/1.99  fof(f60,plain,(
% 11.62/1.99    k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3)),
% 11.62/1.99    inference(cnf_transformation,[],[f34])).
% 11.62/1.99  
% 11.62/1.99  fof(f10,axiom,(
% 11.62/1.99    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 11.62/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.99  
% 11.62/1.99  fof(f49,plain,(
% 11.62/1.99    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 11.62/1.99    inference(cnf_transformation,[],[f10])).
% 11.62/1.99  
% 11.62/1.99  fof(f11,axiom,(
% 11.62/1.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 11.62/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.99  
% 11.62/1.99  fof(f50,plain,(
% 11.62/1.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 11.62/1.99    inference(cnf_transformation,[],[f11])).
% 11.62/1.99  
% 11.62/1.99  fof(f12,axiom,(
% 11.62/1.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 11.62/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.99  
% 11.62/1.99  fof(f51,plain,(
% 11.62/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 11.62/1.99    inference(cnf_transformation,[],[f12])).
% 11.62/1.99  
% 11.62/1.99  fof(f13,axiom,(
% 11.62/1.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.62/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.99  
% 11.62/1.99  fof(f52,plain,(
% 11.62/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.62/1.99    inference(cnf_transformation,[],[f13])).
% 11.62/1.99  
% 11.62/1.99  fof(f14,axiom,(
% 11.62/1.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 11.62/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.99  
% 11.62/1.99  fof(f53,plain,(
% 11.62/1.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 11.62/1.99    inference(cnf_transformation,[],[f14])).
% 11.62/1.99  
% 11.62/1.99  fof(f15,axiom,(
% 11.62/1.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 11.62/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.99  
% 11.62/1.99  fof(f54,plain,(
% 11.62/1.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 11.62/1.99    inference(cnf_transformation,[],[f15])).
% 11.62/1.99  
% 11.62/1.99  fof(f16,axiom,(
% 11.62/1.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 11.62/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.99  
% 11.62/1.99  fof(f55,plain,(
% 11.62/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 11.62/1.99    inference(cnf_transformation,[],[f16])).
% 11.62/1.99  
% 11.62/1.99  fof(f17,axiom,(
% 11.62/1.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 11.62/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.99  
% 11.62/1.99  fof(f56,plain,(
% 11.62/1.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 11.62/1.99    inference(cnf_transformation,[],[f17])).
% 11.62/1.99  
% 11.62/1.99  fof(f61,plain,(
% 11.62/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 11.62/1.99    inference(definition_unfolding,[],[f55,f56])).
% 11.62/1.99  
% 11.62/1.99  fof(f62,plain,(
% 11.62/1.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 11.62/1.99    inference(definition_unfolding,[],[f54,f61])).
% 11.62/1.99  
% 11.62/1.99  fof(f63,plain,(
% 11.62/1.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 11.62/1.99    inference(definition_unfolding,[],[f53,f62])).
% 11.62/1.99  
% 11.62/1.99  fof(f64,plain,(
% 11.62/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 11.62/1.99    inference(definition_unfolding,[],[f52,f63])).
% 11.62/1.99  
% 11.62/1.99  fof(f65,plain,(
% 11.62/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 11.62/1.99    inference(definition_unfolding,[],[f51,f64])).
% 11.62/1.99  
% 11.62/1.99  fof(f66,plain,(
% 11.62/1.99    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 11.62/1.99    inference(definition_unfolding,[],[f50,f65])).
% 11.62/1.99  
% 11.62/1.99  fof(f76,plain,(
% 11.62/1.99    k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0),
% 11.62/1.99    inference(definition_unfolding,[],[f60,f49,f66])).
% 11.62/1.99  
% 11.62/1.99  fof(f8,axiom,(
% 11.62/1.99    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 11.62/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.99  
% 11.62/1.99  fof(f47,plain,(
% 11.62/1.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 11.62/1.99    inference(cnf_transformation,[],[f8])).
% 11.62/1.99  
% 11.62/1.99  fof(f2,axiom,(
% 11.62/1.99    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 11.62/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.99  
% 11.62/1.99  fof(f36,plain,(
% 11.62/1.99    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 11.62/1.99    inference(cnf_transformation,[],[f2])).
% 11.62/1.99  
% 11.62/1.99  fof(f9,axiom,(
% 11.62/1.99    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 11.62/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.99  
% 11.62/1.99  fof(f48,plain,(
% 11.62/1.99    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 11.62/1.99    inference(cnf_transformation,[],[f9])).
% 11.62/1.99  
% 11.62/1.99  fof(f7,axiom,(
% 11.62/1.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 11.62/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.99  
% 11.62/1.99  fof(f46,plain,(
% 11.62/1.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.62/1.99    inference(cnf_transformation,[],[f7])).
% 11.62/1.99  
% 11.62/1.99  fof(f3,axiom,(
% 11.62/1.99    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 11.62/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.99  
% 11.62/1.99  fof(f25,plain,(
% 11.62/1.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.62/1.99    inference(nnf_transformation,[],[f3])).
% 11.62/1.99  
% 11.62/1.99  fof(f26,plain,(
% 11.62/1.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.62/1.99    inference(flattening,[],[f25])).
% 11.62/1.99  
% 11.62/1.99  fof(f27,plain,(
% 11.62/1.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.62/1.99    inference(rectify,[],[f26])).
% 11.62/1.99  
% 11.62/1.99  fof(f28,plain,(
% 11.62/1.99    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 11.62/1.99    introduced(choice_axiom,[])).
% 11.62/1.99  
% 11.62/1.99  fof(f29,plain,(
% 11.62/1.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.62/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 11.62/1.99  
% 11.62/1.99  fof(f38,plain,(
% 11.62/1.99    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 11.62/1.99    inference(cnf_transformation,[],[f29])).
% 11.62/1.99  
% 11.62/1.99  fof(f6,axiom,(
% 11.62/1.99    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 11.62/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.99  
% 11.62/1.99  fof(f45,plain,(
% 11.62/1.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 11.62/1.99    inference(cnf_transformation,[],[f6])).
% 11.62/1.99  
% 11.62/1.99  fof(f71,plain,(
% 11.62/1.99    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 11.62/1.99    inference(definition_unfolding,[],[f38,f45])).
% 11.62/1.99  
% 11.62/1.99  fof(f78,plain,(
% 11.62/1.99    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 11.62/1.99    inference(equality_resolution,[],[f71])).
% 11.62/1.99  
% 11.62/1.99  fof(f4,axiom,(
% 11.62/1.99    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 11.62/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.99  
% 11.62/1.99  fof(f22,plain,(
% 11.62/1.99    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 11.62/1.99    inference(rectify,[],[f4])).
% 11.62/1.99  
% 11.62/1.99  fof(f43,plain,(
% 11.62/1.99    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 11.62/1.99    inference(cnf_transformation,[],[f22])).
% 11.62/1.99  
% 11.62/1.99  fof(f37,plain,(
% 11.62/1.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 11.62/1.99    inference(cnf_transformation,[],[f29])).
% 11.62/1.99  
% 11.62/1.99  fof(f72,plain,(
% 11.62/1.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 11.62/1.99    inference(definition_unfolding,[],[f37,f45])).
% 11.62/1.99  
% 11.62/1.99  fof(f79,plain,(
% 11.62/1.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 11.62/1.99    inference(equality_resolution,[],[f72])).
% 11.62/1.99  
% 11.62/1.99  fof(f19,axiom,(
% 11.62/1.99    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 11.62/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.99  
% 11.62/1.99  fof(f32,plain,(
% 11.62/1.99    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 11.62/1.99    inference(nnf_transformation,[],[f19])).
% 11.62/1.99  
% 11.62/1.99  fof(f58,plain,(
% 11.62/1.99    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 11.62/1.99    inference(cnf_transformation,[],[f32])).
% 11.62/1.99  
% 11.62/1.99  fof(f75,plain,(
% 11.62/1.99    ( ! [X0,X1] : (X0 != X1 | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 11.62/1.99    inference(definition_unfolding,[],[f58,f45,f66,f66,f66])).
% 11.62/1.99  
% 11.62/1.99  fof(f80,plain,(
% 11.62/1.99    ( ! [X1] : (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 11.62/1.99    inference(equality_resolution,[],[f75])).
% 11.62/1.99  
% 11.62/1.99  cnf(c_9,plain,
% 11.62/1.99      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 11.62/1.99      inference(cnf_transformation,[],[f44]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_39134,plain,
% 11.62/1.99      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 11.62/1.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_0,plain,
% 11.62/1.99      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 11.62/1.99      inference(cnf_transformation,[],[f35]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_16,negated_conjecture,
% 11.62/1.99      ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0 ),
% 11.62/1.99      inference(cnf_transformation,[],[f76]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_11,plain,
% 11.62/1.99      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 11.62/1.99      inference(cnf_transformation,[],[f47]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_1,plain,
% 11.62/1.99      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 11.62/1.99      inference(cnf_transformation,[],[f36]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_101,negated_conjecture,
% 11.62/1.99      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = k1_xboole_0 ),
% 11.62/1.99      inference(theory_normalisation,[status(thm)],[c_16,c_11,c_1]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_39232,plain,
% 11.62/1.99      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k1_xboole_0 ),
% 11.62/1.99      inference(demodulation,[status(thm)],[c_0,c_101]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_12,plain,
% 11.62/1.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.62/1.99      inference(cnf_transformation,[],[f48]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_39254,plain,
% 11.62/1.99      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 11.62/1.99      inference(superposition,[status(thm)],[c_12,c_11]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_10,plain,
% 11.62/1.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.62/1.99      inference(cnf_transformation,[],[f46]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_39237,plain,
% 11.62/1.99      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 11.62/1.99      inference(superposition,[status(thm)],[c_10,c_1]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_39554,plain,
% 11.62/1.99      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 11.62/1.99      inference(demodulation,[status(thm)],[c_39254,c_39237]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_39565,plain,
% 11.62/1.99      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k5_xboole_0(sK3,k1_xboole_0) ),
% 11.62/1.99      inference(superposition,[status(thm)],[c_39232,c_39554]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_39584,plain,
% 11.62/1.99      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = sK3 ),
% 11.62/1.99      inference(demodulation,[status(thm)],[c_39565,c_10]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_6,negated_conjecture,
% 11.62/1.99      ( ~ r2_hidden(X0,X1)
% 11.62/1.99      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 11.62/1.99      inference(cnf_transformation,[],[f78]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_39136,plain,
% 11.62/1.99      ( r2_hidden(X0,X1) != iProver_top
% 11.62/1.99      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 11.62/1.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_39233,plain,
% 11.62/1.99      ( r2_hidden(X0,X1) != iProver_top
% 11.62/1.99      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X1,X2))) != iProver_top ),
% 11.62/1.99      inference(superposition,[status(thm)],[c_0,c_39136]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_40327,plain,
% 11.62/1.99      ( r2_hidden(X0,sK3) != iProver_top ),
% 11.62/1.99      inference(superposition,[status(thm)],[c_39584,c_39233]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_40393,plain,
% 11.62/1.99      ( sK3 = k1_xboole_0 ),
% 11.62/1.99      inference(superposition,[status(thm)],[c_39134,c_40327]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_47904,plain,
% 11.62/1.99      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k1_xboole_0 ),
% 11.62/1.99      inference(demodulation,[status(thm)],[c_40393,c_39584]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_39513,plain,
% 11.62/1.99      ( r2_hidden(X0,X1) != iProver_top
% 11.62/1.99      | r2_hidden(X0,k3_xboole_0(k1_xboole_0,X1)) != iProver_top ),
% 11.62/1.99      inference(superposition,[status(thm)],[c_39237,c_39136]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_8,plain,
% 11.62/1.99      ( k3_xboole_0(X0,X0) = X0 ),
% 11.62/1.99      inference(cnf_transformation,[],[f43]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_5080,plain,
% 11.62/1.99      ( r2_hidden(X0,X1) != iProver_top
% 11.62/1.99      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 11.62/1.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_5177,plain,
% 11.62/1.99      ( r2_hidden(X0,X1) != iProver_top
% 11.62/1.99      | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 11.62/1.99      inference(superposition,[status(thm)],[c_8,c_5080]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_5188,plain,
% 11.62/1.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 11.62/1.99      inference(superposition,[status(thm)],[c_10,c_5177]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_5231,plain,
% 11.62/1.99      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 11.62/1.99      inference(superposition,[status(thm)],[c_10,c_1]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_7,plain,
% 11.62/1.99      ( r2_hidden(X0,X1)
% 11.62/1.99      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 11.62/1.99      inference(cnf_transformation,[],[f79]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_5079,plain,
% 11.62/1.99      ( r2_hidden(X0,X1) = iProver_top
% 11.62/1.99      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
% 11.62/1.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_6200,plain,
% 11.62/1.99      ( r2_hidden(X0,k3_xboole_0(k1_xboole_0,X1)) != iProver_top
% 11.62/1.99      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 11.62/1.99      inference(superposition,[status(thm)],[c_5231,c_5079]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_39641,plain,
% 11.62/1.99      ( r2_hidden(X0,k3_xboole_0(k1_xboole_0,X1)) != iProver_top ),
% 11.62/1.99      inference(global_propositional_subsumption,
% 11.62/1.99                [status(thm)],
% 11.62/1.99                [c_39513,c_5188,c_6200]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_39646,plain,
% 11.62/1.99      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.62/1.99      inference(superposition,[status(thm)],[c_39134,c_39641]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_47906,plain,
% 11.62/1.99      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0 ),
% 11.62/1.99      inference(demodulation,[status(thm)],[c_47904,c_10,c_39646]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_15,negated_conjecture,
% 11.62/1.99      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 11.62/1.99      inference(cnf_transformation,[],[f80]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_39174,plain,
% 11.62/1.99      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
% 11.62/1.99      inference(demodulation,[status(thm)],[c_15,c_8,c_12]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_39182,plain,
% 11.62/1.99      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k1_xboole_0 ),
% 11.62/1.99      inference(instantiation,[status(thm)],[c_39174]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(contradiction,plain,
% 11.62/1.99      ( $false ),
% 11.62/1.99      inference(minisat,[status(thm)],[c_47906,c_39182]) ).
% 11.62/1.99  
% 11.62/1.99  
% 11.62/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.62/1.99  
% 11.62/1.99  ------                               Statistics
% 11.62/1.99  
% 11.62/1.99  ------ Selected
% 11.62/1.99  
% 11.62/1.99  total_time:                             1.119
% 11.62/1.99  
%------------------------------------------------------------------------------
