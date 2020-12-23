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
% DateTime   : Thu Dec  3 11:31:43 EST 2020

% Result     : Theorem 15.35s
% Output     : CNFRefutation 15.35s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 388 expanded)
%              Number of clauses        :   30 (  41 expanded)
%              Number of leaves         :   19 ( 123 expanded)
%              Depth                    :   17
%              Number of atoms          :  117 ( 418 expanded)
%              Number of equality atoms :   97 ( 398 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f20])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f70,f80])).

fof(f82,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f69,f81])).

fof(f83,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f68,f82])).

fof(f84,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f67,f83])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f75,f84,f84])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f52])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f85,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f54,f52])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f48,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f79,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f58,f52])).

fof(f98,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f74,f79,f83])).

fof(f23,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(negated_conjecture,[],[f23])).

fof(f34,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(ennf_transformation,[],[f24])).

fof(f45,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))
   => k2_tarski(sK3,sK4) != k3_tarski(k2_tarski(k1_tarski(sK3),k1_tarski(sK4))) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    k2_tarski(sK3,sK4) != k3_tarski(k2_tarski(k1_tarski(sK3),k1_tarski(sK4))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f34,f45])).

fof(f78,plain,(
    k2_tarski(sK3,sK4) != k3_tarski(k2_tarski(k1_tarski(sK3),k1_tarski(sK4))) ),
    inference(cnf_transformation,[],[f46])).

fof(f102,plain,(
    k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k3_tarski(k5_enumset1(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))) ),
    inference(definition_unfolding,[],[f78,f83,f83,f84,f84])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f21])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f76,f84,f84,f83])).

fof(f22,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f101,plain,(
    ! [X0] : k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f77,f84])).

cnf(c_20,plain,
    ( r1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_22322,plain,
    ( X0 = X1
    | r1_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_22328,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_23888,plain,
    ( X0 = X1
    | k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(superposition,[status(thm)],[c_22322,c_22328])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_6,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_22331,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_22618,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_22331])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_22332,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_23527,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_22618,c_22332])).

cnf(c_26716,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_0,c_23527])).

cnf(c_27193,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_26716,c_0])).

cnf(c_40785,plain,
    ( X0 = X1
    | k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) = k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) ),
    inference(superposition,[status(thm)],[c_23888,c_27193])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_40860,plain,
    ( X0 = X1
    | k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(demodulation,[status(thm)],[c_40785,c_1])).

cnf(c_19,plain,
    ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_23,negated_conjecture,
    ( k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k3_tarski(k5_enumset1(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_22837,plain,
    ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) != k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_19,c_23])).

cnf(c_23115,plain,
    ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) != k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4) ),
    inference(superposition,[status(thm)],[c_0,c_22837])).

cnf(c_41596,plain,
    ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | sK4 = sK3 ),
    inference(superposition,[status(thm)],[c_40860,c_23115])).

cnf(c_21,plain,
    ( X0 = X1
    | k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = k5_enumset1(X1,X1,X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_42064,plain,
    ( sK4 = sK3 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_41596,c_21])).

cnf(c_42065,plain,
    ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) != k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_42064,c_23115])).

cnf(c_22,plain,
    ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_22841,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_19,c_22])).

cnf(c_22843,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_22841,c_1])).

cnf(c_42066,plain,
    ( k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_42065,c_1,c_22843])).

cnf(c_42067,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_42066])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:16:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 15.35/2.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.35/2.49  
% 15.35/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.35/2.49  
% 15.35/2.49  ------  iProver source info
% 15.35/2.49  
% 15.35/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.35/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.35/2.49  git: non_committed_changes: false
% 15.35/2.49  git: last_make_outside_of_git: false
% 15.35/2.49  
% 15.35/2.49  ------ 
% 15.35/2.49  ------ Parsing...
% 15.35/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  ------ Proving...
% 15.35/2.49  ------ Problem Properties 
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  clauses                                 24
% 15.35/2.49  conjectures                             1
% 15.35/2.49  EPR                                     0
% 15.35/2.49  Horn                                    18
% 15.35/2.49  unary                                   10
% 15.35/2.49  binary                                  9
% 15.35/2.49  lits                                    46
% 15.35/2.49  lits eq                                 26
% 15.35/2.49  fd_pure                                 0
% 15.35/2.49  fd_pseudo                               0
% 15.35/2.49  fd_cond                                 1
% 15.35/2.49  fd_pseudo_cond                          6
% 15.35/2.49  AC symbols                              0
% 15.35/2.49  
% 15.35/2.49  ------ Input Options Time Limit: Unbounded
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing...
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 15.35/2.49  Current options:
% 15.35/2.49  ------ 
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.35/2.49  
% 15.35/2.49  ------ Proving...
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  % SZS status Theorem for theBenchmark.p
% 15.35/2.49  
% 15.35/2.49   Resolution empty clause
% 15.35/2.49  
% 15.35/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.35/2.49  
% 15.35/2.49  fof(f20,axiom,(
% 15.35/2.49    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 15.35/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.35/2.49  
% 15.35/2.49  fof(f32,plain,(
% 15.35/2.49    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 15.35/2.49    inference(ennf_transformation,[],[f20])).
% 15.35/2.49  
% 15.35/2.49  fof(f75,plain,(
% 15.35/2.49    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 15.35/2.49    inference(cnf_transformation,[],[f32])).
% 15.35/2.49  
% 15.35/2.49  fof(f12,axiom,(
% 15.35/2.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 15.35/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.35/2.49  
% 15.35/2.49  fof(f67,plain,(
% 15.35/2.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 15.35/2.49    inference(cnf_transformation,[],[f12])).
% 15.35/2.49  
% 15.35/2.49  fof(f13,axiom,(
% 15.35/2.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 15.35/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.35/2.49  
% 15.35/2.49  fof(f68,plain,(
% 15.35/2.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 15.35/2.49    inference(cnf_transformation,[],[f13])).
% 15.35/2.49  
% 15.35/2.49  fof(f14,axiom,(
% 15.35/2.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 15.35/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.35/2.49  
% 15.35/2.49  fof(f69,plain,(
% 15.35/2.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 15.35/2.49    inference(cnf_transformation,[],[f14])).
% 15.35/2.49  
% 15.35/2.49  fof(f15,axiom,(
% 15.35/2.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 15.35/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.35/2.49  
% 15.35/2.49  fof(f70,plain,(
% 15.35/2.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 15.35/2.49    inference(cnf_transformation,[],[f15])).
% 15.35/2.49  
% 15.35/2.49  fof(f16,axiom,(
% 15.35/2.49    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 15.35/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.35/2.49  
% 15.35/2.49  fof(f71,plain,(
% 15.35/2.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 15.35/2.49    inference(cnf_transformation,[],[f16])).
% 15.35/2.49  
% 15.35/2.49  fof(f17,axiom,(
% 15.35/2.49    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 15.35/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.35/2.49  
% 15.35/2.49  fof(f72,plain,(
% 15.35/2.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 15.35/2.49    inference(cnf_transformation,[],[f17])).
% 15.35/2.49  
% 15.35/2.49  fof(f80,plain,(
% 15.35/2.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 15.35/2.49    inference(definition_unfolding,[],[f71,f72])).
% 15.35/2.49  
% 15.35/2.49  fof(f81,plain,(
% 15.35/2.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 15.35/2.49    inference(definition_unfolding,[],[f70,f80])).
% 15.35/2.49  
% 15.35/2.49  fof(f82,plain,(
% 15.35/2.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 15.35/2.49    inference(definition_unfolding,[],[f69,f81])).
% 15.35/2.49  
% 15.35/2.49  fof(f83,plain,(
% 15.35/2.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 15.35/2.49    inference(definition_unfolding,[],[f68,f82])).
% 15.35/2.49  
% 15.35/2.49  fof(f84,plain,(
% 15.35/2.49    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 15.35/2.49    inference(definition_unfolding,[],[f67,f83])).
% 15.35/2.49  
% 15.35/2.49  fof(f99,plain,(
% 15.35/2.49    ( ! [X0,X1] : (r1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) | X0 = X1) )),
% 15.35/2.49    inference(definition_unfolding,[],[f75,f84,f84])).
% 15.35/2.49  
% 15.35/2.49  fof(f9,axiom,(
% 15.35/2.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 15.35/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.35/2.49  
% 15.35/2.49  fof(f39,plain,(
% 15.35/2.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 15.35/2.49    inference(nnf_transformation,[],[f9])).
% 15.35/2.49  
% 15.35/2.49  fof(f56,plain,(
% 15.35/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 15.35/2.49    inference(cnf_transformation,[],[f39])).
% 15.35/2.49  
% 15.35/2.49  fof(f5,axiom,(
% 15.35/2.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 15.35/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.35/2.49  
% 15.35/2.49  fof(f52,plain,(
% 15.35/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 15.35/2.49    inference(cnf_transformation,[],[f5])).
% 15.35/2.49  
% 15.35/2.49  fof(f88,plain,(
% 15.35/2.49    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 | ~r1_xboole_0(X0,X1)) )),
% 15.35/2.49    inference(definition_unfolding,[],[f56,f52])).
% 15.35/2.49  
% 15.35/2.49  fof(f1,axiom,(
% 15.35/2.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 15.35/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.35/2.49  
% 15.35/2.49  fof(f47,plain,(
% 15.35/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 15.35/2.49    inference(cnf_transformation,[],[f1])).
% 15.35/2.49  
% 15.35/2.49  fof(f7,axiom,(
% 15.35/2.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 15.35/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.35/2.49  
% 15.35/2.49  fof(f54,plain,(
% 15.35/2.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 15.35/2.49    inference(cnf_transformation,[],[f7])).
% 15.35/2.49  
% 15.35/2.49  fof(f85,plain,(
% 15.35/2.49    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 15.35/2.49    inference(definition_unfolding,[],[f54,f52])).
% 15.35/2.49  
% 15.35/2.49  fof(f6,axiom,(
% 15.35/2.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 15.35/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.35/2.49  
% 15.35/2.49  fof(f29,plain,(
% 15.35/2.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 15.35/2.49    inference(ennf_transformation,[],[f6])).
% 15.35/2.49  
% 15.35/2.49  fof(f53,plain,(
% 15.35/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 15.35/2.49    inference(cnf_transformation,[],[f29])).
% 15.35/2.49  
% 15.35/2.49  fof(f2,axiom,(
% 15.35/2.49    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 15.35/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.35/2.49  
% 15.35/2.49  fof(f25,plain,(
% 15.35/2.49    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 15.35/2.49    inference(rectify,[],[f2])).
% 15.35/2.49  
% 15.35/2.49  fof(f48,plain,(
% 15.35/2.49    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 15.35/2.49    inference(cnf_transformation,[],[f25])).
% 15.35/2.49  
% 15.35/2.49  fof(f19,axiom,(
% 15.35/2.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 15.35/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.35/2.49  
% 15.35/2.49  fof(f74,plain,(
% 15.35/2.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 15.35/2.49    inference(cnf_transformation,[],[f19])).
% 15.35/2.49  
% 15.35/2.49  fof(f10,axiom,(
% 15.35/2.49    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 15.35/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.35/2.49  
% 15.35/2.49  fof(f58,plain,(
% 15.35/2.49    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 15.35/2.49    inference(cnf_transformation,[],[f10])).
% 15.35/2.49  
% 15.35/2.49  fof(f79,plain,(
% 15.35/2.49    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 15.35/2.49    inference(definition_unfolding,[],[f58,f52])).
% 15.35/2.49  
% 15.35/2.49  fof(f98,plain,(
% 15.35/2.49    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 15.35/2.49    inference(definition_unfolding,[],[f74,f79,f83])).
% 15.35/2.49  
% 15.35/2.49  fof(f23,conjecture,(
% 15.35/2.49    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 15.35/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.35/2.49  
% 15.35/2.49  fof(f24,negated_conjecture,(
% 15.35/2.49    ~! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 15.35/2.49    inference(negated_conjecture,[],[f23])).
% 15.35/2.49  
% 15.35/2.49  fof(f34,plain,(
% 15.35/2.49    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 15.35/2.49    inference(ennf_transformation,[],[f24])).
% 15.35/2.49  
% 15.35/2.49  fof(f45,plain,(
% 15.35/2.49    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) => k2_tarski(sK3,sK4) != k3_tarski(k2_tarski(k1_tarski(sK3),k1_tarski(sK4)))),
% 15.35/2.49    introduced(choice_axiom,[])).
% 15.35/2.49  
% 15.35/2.49  fof(f46,plain,(
% 15.35/2.49    k2_tarski(sK3,sK4) != k3_tarski(k2_tarski(k1_tarski(sK3),k1_tarski(sK4)))),
% 15.35/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f34,f45])).
% 15.35/2.49  
% 15.35/2.49  fof(f78,plain,(
% 15.35/2.49    k2_tarski(sK3,sK4) != k3_tarski(k2_tarski(k1_tarski(sK3),k1_tarski(sK4)))),
% 15.35/2.49    inference(cnf_transformation,[],[f46])).
% 15.35/2.49  
% 15.35/2.49  fof(f102,plain,(
% 15.35/2.49    k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k3_tarski(k5_enumset1(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),
% 15.35/2.49    inference(definition_unfolding,[],[f78,f83,f83,f84,f84])).
% 15.35/2.49  
% 15.35/2.49  fof(f21,axiom,(
% 15.35/2.49    ! [X0,X1] : (X0 != X1 => k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1))),
% 15.35/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.35/2.49  
% 15.35/2.49  fof(f33,plain,(
% 15.35/2.49    ! [X0,X1] : (k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) | X0 = X1)),
% 15.35/2.49    inference(ennf_transformation,[],[f21])).
% 15.35/2.49  
% 15.35/2.49  fof(f76,plain,(
% 15.35/2.49    ( ! [X0,X1] : (k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) | X0 = X1) )),
% 15.35/2.49    inference(cnf_transformation,[],[f33])).
% 15.35/2.49  
% 15.35/2.49  fof(f100,plain,(
% 15.35/2.49    ( ! [X0,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) | X0 = X1) )),
% 15.35/2.49    inference(definition_unfolding,[],[f76,f84,f84,f83])).
% 15.35/2.49  
% 15.35/2.49  fof(f22,axiom,(
% 15.35/2.49    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 15.35/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.35/2.49  
% 15.35/2.49  fof(f77,plain,(
% 15.35/2.49    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 15.35/2.49    inference(cnf_transformation,[],[f22])).
% 15.35/2.49  
% 15.35/2.49  fof(f101,plain,(
% 15.35/2.49    ( ! [X0] : (k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 15.35/2.49    inference(definition_unfolding,[],[f77,f84])).
% 15.35/2.49  
% 15.35/2.49  cnf(c_20,plain,
% 15.35/2.49      ( r1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))
% 15.35/2.49      | X1 = X0 ),
% 15.35/2.49      inference(cnf_transformation,[],[f99]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_22322,plain,
% 15.35/2.49      ( X0 = X1
% 15.35/2.49      | r1_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
% 15.35/2.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_9,plain,
% 15.35/2.49      ( ~ r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 15.35/2.49      inference(cnf_transformation,[],[f88]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_22328,plain,
% 15.35/2.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
% 15.35/2.49      | r1_xboole_0(X0,X1) != iProver_top ),
% 15.35/2.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_23888,plain,
% 15.35/2.49      ( X0 = X1
% 15.35/2.49      | k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
% 15.35/2.49      inference(superposition,[status(thm)],[c_22322,c_22328]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_0,plain,
% 15.35/2.49      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 15.35/2.49      inference(cnf_transformation,[],[f47]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_6,plain,
% 15.35/2.49      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 15.35/2.49      inference(cnf_transformation,[],[f85]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_22331,plain,
% 15.35/2.49      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 15.35/2.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_22618,plain,
% 15.35/2.49      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = iProver_top ),
% 15.35/2.49      inference(superposition,[status(thm)],[c_0,c_22331]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_5,plain,
% 15.35/2.49      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 15.35/2.49      inference(cnf_transformation,[],[f53]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_22332,plain,
% 15.35/2.49      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 15.35/2.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_23527,plain,
% 15.35/2.49      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
% 15.35/2.49      inference(superposition,[status(thm)],[c_22618,c_22332]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_26716,plain,
% 15.35/2.49      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
% 15.35/2.49      inference(superposition,[status(thm)],[c_0,c_23527]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_27193,plain,
% 15.35/2.49      ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
% 15.35/2.49      inference(superposition,[status(thm)],[c_26716,c_0]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_40785,plain,
% 15.35/2.49      ( X0 = X1
% 15.35/2.49      | k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) = k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) ),
% 15.35/2.49      inference(superposition,[status(thm)],[c_23888,c_27193]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_1,plain,
% 15.35/2.49      ( k3_xboole_0(X0,X0) = X0 ),
% 15.35/2.49      inference(cnf_transformation,[],[f48]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_40860,plain,
% 15.35/2.49      ( X0 = X1
% 15.35/2.49      | k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
% 15.35/2.49      inference(demodulation,[status(thm)],[c_40785,c_1]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_19,plain,
% 15.35/2.49      ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 15.35/2.49      inference(cnf_transformation,[],[f98]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_23,negated_conjecture,
% 15.35/2.49      ( k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k3_tarski(k5_enumset1(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))) ),
% 15.35/2.49      inference(cnf_transformation,[],[f102]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_22837,plain,
% 15.35/2.49      ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) != k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4) ),
% 15.35/2.49      inference(demodulation,[status(thm)],[c_19,c_23]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_23115,plain,
% 15.35/2.49      ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) != k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4) ),
% 15.35/2.49      inference(superposition,[status(thm)],[c_0,c_22837]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_41596,plain,
% 15.35/2.49      ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 15.35/2.49      | sK4 = sK3 ),
% 15.35/2.49      inference(superposition,[status(thm)],[c_40860,c_23115]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_21,plain,
% 15.35/2.49      ( X0 = X1
% 15.35/2.49      | k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = k5_enumset1(X1,X1,X1,X1,X1,X1,X0) ),
% 15.35/2.49      inference(cnf_transformation,[],[f100]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_42064,plain,
% 15.35/2.49      ( sK4 = sK3 ),
% 15.35/2.49      inference(forward_subsumption_resolution,[status(thm)],[c_41596,c_21]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_42065,plain,
% 15.35/2.49      ( k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) != k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 15.35/2.49      inference(demodulation,[status(thm)],[c_42064,c_23115]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_22,plain,
% 15.35/2.49      ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 15.35/2.49      inference(cnf_transformation,[],[f101]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_22841,plain,
% 15.35/2.49      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
% 15.35/2.49      inference(superposition,[status(thm)],[c_19,c_22]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_22843,plain,
% 15.35/2.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
% 15.35/2.49      inference(light_normalisation,[status(thm)],[c_22841,c_1]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_42066,plain,
% 15.35/2.49      ( k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 15.35/2.49      inference(demodulation,[status(thm)],[c_42065,c_1,c_22843]) ).
% 15.35/2.49  
% 15.35/2.49  cnf(c_42067,plain,
% 15.35/2.49      ( $false ),
% 15.35/2.49      inference(equality_resolution_simp,[status(thm)],[c_42066]) ).
% 15.35/2.49  
% 15.35/2.49  
% 15.35/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.35/2.49  
% 15.35/2.49  ------                               Statistics
% 15.35/2.49  
% 15.35/2.49  ------ Selected
% 15.35/2.49  
% 15.35/2.49  total_time:                             1.543
% 15.35/2.49  
%------------------------------------------------------------------------------
