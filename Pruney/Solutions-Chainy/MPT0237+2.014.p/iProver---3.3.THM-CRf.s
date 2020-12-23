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

% Result     : Theorem 11.14s
% Output     : CNFRefutation 11.14s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 418 expanded)
%              Number of clauses        :   36 (  47 expanded)
%              Number of leaves         :   22 ( 131 expanded)
%              Depth                    :   16
%              Number of atoms          :  150 ( 492 expanded)
%              Number of equality atoms :  106 ( 417 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f21])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f18])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f70,f78])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f69,f79])).

fof(f81,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f68,f80])).

fof(f82,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f67,f81])).

fof(f83,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f66,f82])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f75,f83,f83])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f23,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(negated_conjecture,[],[f23])).

fof(f33,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(ennf_transformation,[],[f24])).

fof(f44,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))
   => k2_tarski(sK3,sK4) != k3_tarski(k2_tarski(k1_tarski(sK3),k1_tarski(sK4))) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    k2_tarski(sK3,sK4) != k3_tarski(k2_tarski(k1_tarski(sK3),k1_tarski(sK4))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f33,f44])).

fof(f77,plain,(
    k2_tarski(sK3,sK4) != k3_tarski(k2_tarski(k1_tarski(sK3),k1_tarski(sK4))) ),
    inference(cnf_transformation,[],[f45])).

fof(f101,plain,(
    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k3_tarski(k6_enumset1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) ),
    inference(definition_unfolding,[],[f77,f82,f82,f83,f83])).

fof(f20,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f98,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f74,f57,f82])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f22])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f76,f83,f83,f82])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f85,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f46,f52,f52])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f34])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f52])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f49,f52])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f47,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f86,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f47,f52])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f84,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f51,f52])).

cnf(c_20,plain,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1247,plain,
    ( X0 = X1
    | r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1257,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1863,plain,
    ( X0 = X1
    | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(superposition,[status(thm)],[c_1247,c_1257])).

cnf(c_22,negated_conjecture,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k3_tarski(k6_enumset1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_19,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1349,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_22,c_19])).

cnf(c_11815,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | sK4 = sK3 ),
    inference(superposition,[status(thm)],[c_1863,c_1349])).

cnf(c_21,plain,
    ( X0 = X1
    | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1707,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1713,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | sK4 = sK3 ),
    inference(instantiation,[status(thm)],[c_1707])).

cnf(c_14557,plain,
    ( sK4 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11815,c_1713])).

cnf(c_14560,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_14557,c_1349])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1259,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1261,plain,
    ( r2_hidden(sK0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4196,plain,
    ( r2_hidden(sK0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_1261])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1262,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5920,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4196,c_1262])).

cnf(c_6153,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1259,c_5920])).

cnf(c_6205,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6153,c_1257])).

cnf(c_1862,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_1259,c_1257])).

cnf(c_1874,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1862,c_1])).

cnf(c_6480,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_6205,c_1874])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1433,plain,
    ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_1443,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_1433])).

cnf(c_6496,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6480,c_1443])).

cnf(c_14561,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_14560,c_6,c_6496])).

cnf(c_14562,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_14561])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:24:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  % Running in FOF mode
% 11.14/2.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.14/2.01  
% 11.14/2.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.14/2.01  
% 11.14/2.01  ------  iProver source info
% 11.14/2.01  
% 11.14/2.01  git: date: 2020-06-30 10:37:57 +0100
% 11.14/2.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.14/2.01  git: non_committed_changes: false
% 11.14/2.01  git: last_make_outside_of_git: false
% 11.14/2.01  
% 11.14/2.01  ------ 
% 11.14/2.01  
% 11.14/2.01  ------ Input Options
% 11.14/2.01  
% 11.14/2.01  --out_options                           all
% 11.14/2.01  --tptp_safe_out                         true
% 11.14/2.01  --problem_path                          ""
% 11.14/2.01  --include_path                          ""
% 11.14/2.01  --clausifier                            res/vclausify_rel
% 11.14/2.01  --clausifier_options                    --mode clausify
% 11.14/2.01  --stdin                                 false
% 11.14/2.01  --stats_out                             all
% 11.14/2.01  
% 11.14/2.01  ------ General Options
% 11.14/2.01  
% 11.14/2.01  --fof                                   false
% 11.14/2.01  --time_out_real                         305.
% 11.14/2.01  --time_out_virtual                      -1.
% 11.14/2.01  --symbol_type_check                     false
% 11.14/2.01  --clausify_out                          false
% 11.14/2.01  --sig_cnt_out                           false
% 11.14/2.01  --trig_cnt_out                          false
% 11.14/2.01  --trig_cnt_out_tolerance                1.
% 11.14/2.01  --trig_cnt_out_sk_spl                   false
% 11.14/2.01  --abstr_cl_out                          false
% 11.14/2.01  
% 11.14/2.01  ------ Global Options
% 11.14/2.01  
% 11.14/2.01  --schedule                              default
% 11.14/2.01  --add_important_lit                     false
% 11.14/2.01  --prop_solver_per_cl                    1000
% 11.14/2.01  --min_unsat_core                        false
% 11.14/2.01  --soft_assumptions                      false
% 11.14/2.01  --soft_lemma_size                       3
% 11.14/2.01  --prop_impl_unit_size                   0
% 11.14/2.01  --prop_impl_unit                        []
% 11.14/2.01  --share_sel_clauses                     true
% 11.14/2.01  --reset_solvers                         false
% 11.14/2.01  --bc_imp_inh                            [conj_cone]
% 11.14/2.01  --conj_cone_tolerance                   3.
% 11.14/2.01  --extra_neg_conj                        none
% 11.14/2.01  --large_theory_mode                     true
% 11.14/2.01  --prolific_symb_bound                   200
% 11.14/2.01  --lt_threshold                          2000
% 11.14/2.01  --clause_weak_htbl                      true
% 11.14/2.01  --gc_record_bc_elim                     false
% 11.14/2.01  
% 11.14/2.01  ------ Preprocessing Options
% 11.14/2.01  
% 11.14/2.01  --preprocessing_flag                    true
% 11.14/2.01  --time_out_prep_mult                    0.1
% 11.14/2.01  --splitting_mode                        input
% 11.14/2.01  --splitting_grd                         true
% 11.14/2.01  --splitting_cvd                         false
% 11.14/2.01  --splitting_cvd_svl                     false
% 11.14/2.01  --splitting_nvd                         32
% 11.14/2.01  --sub_typing                            true
% 11.14/2.01  --prep_gs_sim                           true
% 11.14/2.01  --prep_unflatten                        true
% 11.14/2.01  --prep_res_sim                          true
% 11.14/2.01  --prep_upred                            true
% 11.14/2.01  --prep_sem_filter                       exhaustive
% 11.14/2.01  --prep_sem_filter_out                   false
% 11.14/2.01  --pred_elim                             true
% 11.14/2.01  --res_sim_input                         true
% 11.14/2.01  --eq_ax_congr_red                       true
% 11.14/2.01  --pure_diseq_elim                       true
% 11.14/2.01  --brand_transform                       false
% 11.14/2.01  --non_eq_to_eq                          false
% 11.14/2.01  --prep_def_merge                        true
% 11.14/2.01  --prep_def_merge_prop_impl              false
% 11.14/2.01  --prep_def_merge_mbd                    true
% 11.14/2.01  --prep_def_merge_tr_red                 false
% 11.14/2.01  --prep_def_merge_tr_cl                  false
% 11.14/2.01  --smt_preprocessing                     true
% 11.14/2.01  --smt_ac_axioms                         fast
% 11.14/2.01  --preprocessed_out                      false
% 11.14/2.01  --preprocessed_stats                    false
% 11.14/2.01  
% 11.14/2.01  ------ Abstraction refinement Options
% 11.14/2.01  
% 11.14/2.01  --abstr_ref                             []
% 11.14/2.01  --abstr_ref_prep                        false
% 11.14/2.01  --abstr_ref_until_sat                   false
% 11.14/2.01  --abstr_ref_sig_restrict                funpre
% 11.14/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 11.14/2.01  --abstr_ref_under                       []
% 11.14/2.01  
% 11.14/2.01  ------ SAT Options
% 11.14/2.01  
% 11.14/2.01  --sat_mode                              false
% 11.14/2.01  --sat_fm_restart_options                ""
% 11.14/2.01  --sat_gr_def                            false
% 11.14/2.01  --sat_epr_types                         true
% 11.14/2.01  --sat_non_cyclic_types                  false
% 11.14/2.01  --sat_finite_models                     false
% 11.14/2.01  --sat_fm_lemmas                         false
% 11.14/2.01  --sat_fm_prep                           false
% 11.14/2.01  --sat_fm_uc_incr                        true
% 11.14/2.01  --sat_out_model                         small
% 11.14/2.01  --sat_out_clauses                       false
% 11.14/2.01  
% 11.14/2.01  ------ QBF Options
% 11.14/2.01  
% 11.14/2.01  --qbf_mode                              false
% 11.14/2.01  --qbf_elim_univ                         false
% 11.14/2.01  --qbf_dom_inst                          none
% 11.14/2.01  --qbf_dom_pre_inst                      false
% 11.14/2.01  --qbf_sk_in                             false
% 11.14/2.01  --qbf_pred_elim                         true
% 11.14/2.01  --qbf_split                             512
% 11.14/2.01  
% 11.14/2.01  ------ BMC1 Options
% 11.14/2.01  
% 11.14/2.01  --bmc1_incremental                      false
% 11.14/2.01  --bmc1_axioms                           reachable_all
% 11.14/2.01  --bmc1_min_bound                        0
% 11.14/2.01  --bmc1_max_bound                        -1
% 11.14/2.01  --bmc1_max_bound_default                -1
% 11.14/2.01  --bmc1_symbol_reachability              true
% 11.14/2.01  --bmc1_property_lemmas                  false
% 11.14/2.01  --bmc1_k_induction                      false
% 11.14/2.01  --bmc1_non_equiv_states                 false
% 11.14/2.01  --bmc1_deadlock                         false
% 11.14/2.01  --bmc1_ucm                              false
% 11.14/2.01  --bmc1_add_unsat_core                   none
% 11.14/2.01  --bmc1_unsat_core_children              false
% 11.14/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 11.14/2.01  --bmc1_out_stat                         full
% 11.14/2.01  --bmc1_ground_init                      false
% 11.14/2.01  --bmc1_pre_inst_next_state              false
% 11.14/2.01  --bmc1_pre_inst_state                   false
% 11.14/2.01  --bmc1_pre_inst_reach_state             false
% 11.14/2.01  --bmc1_out_unsat_core                   false
% 11.14/2.01  --bmc1_aig_witness_out                  false
% 11.14/2.01  --bmc1_verbose                          false
% 11.14/2.01  --bmc1_dump_clauses_tptp                false
% 11.14/2.01  --bmc1_dump_unsat_core_tptp             false
% 11.14/2.01  --bmc1_dump_file                        -
% 11.14/2.01  --bmc1_ucm_expand_uc_limit              128
% 11.14/2.01  --bmc1_ucm_n_expand_iterations          6
% 11.14/2.01  --bmc1_ucm_extend_mode                  1
% 11.14/2.01  --bmc1_ucm_init_mode                    2
% 11.14/2.01  --bmc1_ucm_cone_mode                    none
% 11.14/2.01  --bmc1_ucm_reduced_relation_type        0
% 11.14/2.01  --bmc1_ucm_relax_model                  4
% 11.14/2.01  --bmc1_ucm_full_tr_after_sat            true
% 11.14/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 11.14/2.01  --bmc1_ucm_layered_model                none
% 11.14/2.01  --bmc1_ucm_max_lemma_size               10
% 11.14/2.01  
% 11.14/2.01  ------ AIG Options
% 11.14/2.01  
% 11.14/2.01  --aig_mode                              false
% 11.14/2.01  
% 11.14/2.01  ------ Instantiation Options
% 11.14/2.01  
% 11.14/2.01  --instantiation_flag                    true
% 11.14/2.01  --inst_sos_flag                         false
% 11.14/2.01  --inst_sos_phase                        true
% 11.14/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.14/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.14/2.01  --inst_lit_sel_side                     num_symb
% 11.14/2.01  --inst_solver_per_active                1400
% 11.14/2.01  --inst_solver_calls_frac                1.
% 11.14/2.01  --inst_passive_queue_type               priority_queues
% 11.14/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.14/2.01  --inst_passive_queues_freq              [25;2]
% 11.14/2.01  --inst_dismatching                      true
% 11.14/2.01  --inst_eager_unprocessed_to_passive     true
% 11.14/2.01  --inst_prop_sim_given                   true
% 11.14/2.01  --inst_prop_sim_new                     false
% 11.14/2.01  --inst_subs_new                         false
% 11.14/2.01  --inst_eq_res_simp                      false
% 11.14/2.01  --inst_subs_given                       false
% 11.14/2.01  --inst_orphan_elimination               true
% 11.14/2.01  --inst_learning_loop_flag               true
% 11.14/2.01  --inst_learning_start                   3000
% 11.14/2.01  --inst_learning_factor                  2
% 11.14/2.01  --inst_start_prop_sim_after_learn       3
% 11.14/2.01  --inst_sel_renew                        solver
% 11.14/2.01  --inst_lit_activity_flag                true
% 11.14/2.01  --inst_restr_to_given                   false
% 11.14/2.01  --inst_activity_threshold               500
% 11.14/2.01  --inst_out_proof                        true
% 11.14/2.01  
% 11.14/2.01  ------ Resolution Options
% 11.14/2.01  
% 11.14/2.01  --resolution_flag                       true
% 11.14/2.01  --res_lit_sel                           adaptive
% 11.14/2.01  --res_lit_sel_side                      none
% 11.14/2.01  --res_ordering                          kbo
% 11.14/2.01  --res_to_prop_solver                    active
% 11.14/2.01  --res_prop_simpl_new                    false
% 11.14/2.01  --res_prop_simpl_given                  true
% 11.14/2.01  --res_passive_queue_type                priority_queues
% 11.14/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.14/2.01  --res_passive_queues_freq               [15;5]
% 11.14/2.01  --res_forward_subs                      full
% 11.14/2.01  --res_backward_subs                     full
% 11.14/2.01  --res_forward_subs_resolution           true
% 11.14/2.01  --res_backward_subs_resolution          true
% 11.14/2.01  --res_orphan_elimination                true
% 11.14/2.01  --res_time_limit                        2.
% 11.14/2.01  --res_out_proof                         true
% 11.14/2.01  
% 11.14/2.01  ------ Superposition Options
% 11.14/2.01  
% 11.14/2.01  --superposition_flag                    true
% 11.14/2.01  --sup_passive_queue_type                priority_queues
% 11.14/2.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.14/2.01  --sup_passive_queues_freq               [8;1;4]
% 11.14/2.01  --demod_completeness_check              fast
% 11.14/2.01  --demod_use_ground                      true
% 11.14/2.01  --sup_to_prop_solver                    passive
% 11.14/2.01  --sup_prop_simpl_new                    true
% 11.14/2.01  --sup_prop_simpl_given                  true
% 11.14/2.01  --sup_fun_splitting                     false
% 11.14/2.01  --sup_smt_interval                      50000
% 11.14/2.01  
% 11.14/2.01  ------ Superposition Simplification Setup
% 11.14/2.01  
% 11.14/2.01  --sup_indices_passive                   []
% 11.14/2.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.14/2.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.14/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.14/2.01  --sup_full_triv                         [TrivRules;PropSubs]
% 11.14/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.14/2.01  --sup_full_bw                           [BwDemod]
% 11.14/2.01  --sup_immed_triv                        [TrivRules]
% 11.14/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.14/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.14/2.01  --sup_immed_bw_main                     []
% 11.14/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.14/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 11.14/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.14/2.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.14/2.01  
% 11.14/2.01  ------ Combination Options
% 11.14/2.01  
% 11.14/2.01  --comb_res_mult                         3
% 11.14/2.01  --comb_sup_mult                         2
% 11.14/2.01  --comb_inst_mult                        10
% 11.14/2.01  
% 11.14/2.01  ------ Debug Options
% 11.14/2.01  
% 11.14/2.01  --dbg_backtrace                         false
% 11.14/2.01  --dbg_dump_prop_clauses                 false
% 11.14/2.01  --dbg_dump_prop_clauses_file            -
% 11.14/2.01  --dbg_out_stat                          false
% 11.14/2.01  ------ Parsing...
% 11.14/2.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.14/2.01  
% 11.14/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.14/2.01  
% 11.14/2.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.14/2.01  
% 11.14/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.14/2.01  ------ Proving...
% 11.14/2.01  ------ Problem Properties 
% 11.14/2.01  
% 11.14/2.01  
% 11.14/2.01  clauses                                 23
% 11.14/2.01  conjectures                             1
% 11.14/2.01  EPR                                     1
% 11.14/2.01  Horn                                    17
% 11.14/2.01  unary                                   10
% 11.14/2.01  binary                                  8
% 11.14/2.01  lits                                    44
% 11.14/2.01  lits eq                                 26
% 11.14/2.01  fd_pure                                 0
% 11.14/2.01  fd_pseudo                               0
% 11.14/2.01  fd_cond                                 1
% 11.14/2.01  fd_pseudo_cond                          6
% 11.14/2.01  AC symbols                              0
% 11.14/2.01  
% 11.14/2.01  ------ Schedule dynamic 5 is on 
% 11.14/2.01  
% 11.14/2.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.14/2.01  
% 11.14/2.01  
% 11.14/2.01  ------ 
% 11.14/2.01  Current options:
% 11.14/2.01  ------ 
% 11.14/2.01  
% 11.14/2.01  ------ Input Options
% 11.14/2.01  
% 11.14/2.01  --out_options                           all
% 11.14/2.01  --tptp_safe_out                         true
% 11.14/2.01  --problem_path                          ""
% 11.14/2.01  --include_path                          ""
% 11.14/2.01  --clausifier                            res/vclausify_rel
% 11.14/2.01  --clausifier_options                    --mode clausify
% 11.14/2.01  --stdin                                 false
% 11.14/2.01  --stats_out                             all
% 11.14/2.01  
% 11.14/2.01  ------ General Options
% 11.14/2.01  
% 11.14/2.01  --fof                                   false
% 11.14/2.01  --time_out_real                         305.
% 11.14/2.01  --time_out_virtual                      -1.
% 11.14/2.01  --symbol_type_check                     false
% 11.14/2.01  --clausify_out                          false
% 11.14/2.01  --sig_cnt_out                           false
% 11.14/2.01  --trig_cnt_out                          false
% 11.14/2.01  --trig_cnt_out_tolerance                1.
% 11.14/2.01  --trig_cnt_out_sk_spl                   false
% 11.14/2.01  --abstr_cl_out                          false
% 11.14/2.01  
% 11.14/2.01  ------ Global Options
% 11.14/2.01  
% 11.14/2.01  --schedule                              default
% 11.14/2.01  --add_important_lit                     false
% 11.14/2.01  --prop_solver_per_cl                    1000
% 11.14/2.01  --min_unsat_core                        false
% 11.14/2.01  --soft_assumptions                      false
% 11.14/2.01  --soft_lemma_size                       3
% 11.14/2.01  --prop_impl_unit_size                   0
% 11.14/2.01  --prop_impl_unit                        []
% 11.14/2.01  --share_sel_clauses                     true
% 11.14/2.01  --reset_solvers                         false
% 11.14/2.01  --bc_imp_inh                            [conj_cone]
% 11.14/2.01  --conj_cone_tolerance                   3.
% 11.14/2.01  --extra_neg_conj                        none
% 11.14/2.01  --large_theory_mode                     true
% 11.14/2.01  --prolific_symb_bound                   200
% 11.14/2.01  --lt_threshold                          2000
% 11.14/2.01  --clause_weak_htbl                      true
% 11.14/2.01  --gc_record_bc_elim                     false
% 11.14/2.01  
% 11.14/2.01  ------ Preprocessing Options
% 11.14/2.01  
% 11.14/2.01  --preprocessing_flag                    true
% 11.14/2.01  --time_out_prep_mult                    0.1
% 11.14/2.01  --splitting_mode                        input
% 11.14/2.01  --splitting_grd                         true
% 11.14/2.01  --splitting_cvd                         false
% 11.14/2.01  --splitting_cvd_svl                     false
% 11.14/2.01  --splitting_nvd                         32
% 11.14/2.01  --sub_typing                            true
% 11.14/2.01  --prep_gs_sim                           true
% 11.14/2.01  --prep_unflatten                        true
% 11.14/2.01  --prep_res_sim                          true
% 11.14/2.01  --prep_upred                            true
% 11.14/2.01  --prep_sem_filter                       exhaustive
% 11.14/2.01  --prep_sem_filter_out                   false
% 11.14/2.01  --pred_elim                             true
% 11.14/2.01  --res_sim_input                         true
% 11.14/2.01  --eq_ax_congr_red                       true
% 11.14/2.01  --pure_diseq_elim                       true
% 11.14/2.01  --brand_transform                       false
% 11.14/2.01  --non_eq_to_eq                          false
% 11.14/2.01  --prep_def_merge                        true
% 11.14/2.01  --prep_def_merge_prop_impl              false
% 11.14/2.01  --prep_def_merge_mbd                    true
% 11.14/2.01  --prep_def_merge_tr_red                 false
% 11.14/2.01  --prep_def_merge_tr_cl                  false
% 11.14/2.01  --smt_preprocessing                     true
% 11.14/2.01  --smt_ac_axioms                         fast
% 11.14/2.01  --preprocessed_out                      false
% 11.14/2.01  --preprocessed_stats                    false
% 11.14/2.01  
% 11.14/2.01  ------ Abstraction refinement Options
% 11.14/2.01  
% 11.14/2.01  --abstr_ref                             []
% 11.14/2.01  --abstr_ref_prep                        false
% 11.14/2.01  --abstr_ref_until_sat                   false
% 11.14/2.01  --abstr_ref_sig_restrict                funpre
% 11.14/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 11.14/2.01  --abstr_ref_under                       []
% 11.14/2.01  
% 11.14/2.01  ------ SAT Options
% 11.14/2.01  
% 11.14/2.01  --sat_mode                              false
% 11.14/2.01  --sat_fm_restart_options                ""
% 11.14/2.01  --sat_gr_def                            false
% 11.14/2.01  --sat_epr_types                         true
% 11.14/2.01  --sat_non_cyclic_types                  false
% 11.14/2.01  --sat_finite_models                     false
% 11.14/2.01  --sat_fm_lemmas                         false
% 11.14/2.01  --sat_fm_prep                           false
% 11.14/2.01  --sat_fm_uc_incr                        true
% 11.14/2.01  --sat_out_model                         small
% 11.14/2.01  --sat_out_clauses                       false
% 11.14/2.01  
% 11.14/2.01  ------ QBF Options
% 11.14/2.01  
% 11.14/2.01  --qbf_mode                              false
% 11.14/2.01  --qbf_elim_univ                         false
% 11.14/2.01  --qbf_dom_inst                          none
% 11.14/2.01  --qbf_dom_pre_inst                      false
% 11.14/2.01  --qbf_sk_in                             false
% 11.14/2.01  --qbf_pred_elim                         true
% 11.14/2.01  --qbf_split                             512
% 11.14/2.01  
% 11.14/2.01  ------ BMC1 Options
% 11.14/2.01  
% 11.14/2.01  --bmc1_incremental                      false
% 11.14/2.01  --bmc1_axioms                           reachable_all
% 11.14/2.01  --bmc1_min_bound                        0
% 11.14/2.01  --bmc1_max_bound                        -1
% 11.14/2.01  --bmc1_max_bound_default                -1
% 11.14/2.01  --bmc1_symbol_reachability              true
% 11.14/2.01  --bmc1_property_lemmas                  false
% 11.14/2.01  --bmc1_k_induction                      false
% 11.14/2.01  --bmc1_non_equiv_states                 false
% 11.14/2.01  --bmc1_deadlock                         false
% 11.14/2.01  --bmc1_ucm                              false
% 11.14/2.01  --bmc1_add_unsat_core                   none
% 11.14/2.01  --bmc1_unsat_core_children              false
% 11.14/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 11.14/2.01  --bmc1_out_stat                         full
% 11.14/2.01  --bmc1_ground_init                      false
% 11.14/2.01  --bmc1_pre_inst_next_state              false
% 11.14/2.01  --bmc1_pre_inst_state                   false
% 11.14/2.01  --bmc1_pre_inst_reach_state             false
% 11.14/2.01  --bmc1_out_unsat_core                   false
% 11.14/2.01  --bmc1_aig_witness_out                  false
% 11.14/2.01  --bmc1_verbose                          false
% 11.14/2.01  --bmc1_dump_clauses_tptp                false
% 11.14/2.01  --bmc1_dump_unsat_core_tptp             false
% 11.14/2.01  --bmc1_dump_file                        -
% 11.14/2.01  --bmc1_ucm_expand_uc_limit              128
% 11.14/2.01  --bmc1_ucm_n_expand_iterations          6
% 11.14/2.01  --bmc1_ucm_extend_mode                  1
% 11.14/2.01  --bmc1_ucm_init_mode                    2
% 11.14/2.01  --bmc1_ucm_cone_mode                    none
% 11.14/2.01  --bmc1_ucm_reduced_relation_type        0
% 11.14/2.01  --bmc1_ucm_relax_model                  4
% 11.14/2.01  --bmc1_ucm_full_tr_after_sat            true
% 11.14/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 11.14/2.01  --bmc1_ucm_layered_model                none
% 11.14/2.01  --bmc1_ucm_max_lemma_size               10
% 11.14/2.01  
% 11.14/2.01  ------ AIG Options
% 11.14/2.01  
% 11.14/2.01  --aig_mode                              false
% 11.14/2.01  
% 11.14/2.01  ------ Instantiation Options
% 11.14/2.01  
% 11.14/2.01  --instantiation_flag                    true
% 11.14/2.01  --inst_sos_flag                         false
% 11.14/2.01  --inst_sos_phase                        true
% 11.14/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.14/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.14/2.01  --inst_lit_sel_side                     none
% 11.14/2.01  --inst_solver_per_active                1400
% 11.14/2.01  --inst_solver_calls_frac                1.
% 11.14/2.01  --inst_passive_queue_type               priority_queues
% 11.14/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.14/2.01  --inst_passive_queues_freq              [25;2]
% 11.14/2.01  --inst_dismatching                      true
% 11.14/2.01  --inst_eager_unprocessed_to_passive     true
% 11.14/2.01  --inst_prop_sim_given                   true
% 11.14/2.01  --inst_prop_sim_new                     false
% 11.14/2.01  --inst_subs_new                         false
% 11.14/2.01  --inst_eq_res_simp                      false
% 11.14/2.01  --inst_subs_given                       false
% 11.14/2.01  --inst_orphan_elimination               true
% 11.14/2.01  --inst_learning_loop_flag               true
% 11.14/2.01  --inst_learning_start                   3000
% 11.14/2.01  --inst_learning_factor                  2
% 11.14/2.01  --inst_start_prop_sim_after_learn       3
% 11.14/2.01  --inst_sel_renew                        solver
% 11.14/2.01  --inst_lit_activity_flag                true
% 11.14/2.01  --inst_restr_to_given                   false
% 11.14/2.01  --inst_activity_threshold               500
% 11.14/2.01  --inst_out_proof                        true
% 11.14/2.01  
% 11.14/2.01  ------ Resolution Options
% 11.14/2.01  
% 11.14/2.01  --resolution_flag                       false
% 11.14/2.01  --res_lit_sel                           adaptive
% 11.14/2.01  --res_lit_sel_side                      none
% 11.14/2.01  --res_ordering                          kbo
% 11.14/2.01  --res_to_prop_solver                    active
% 11.14/2.01  --res_prop_simpl_new                    false
% 11.14/2.01  --res_prop_simpl_given                  true
% 11.14/2.01  --res_passive_queue_type                priority_queues
% 11.14/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.14/2.01  --res_passive_queues_freq               [15;5]
% 11.14/2.01  --res_forward_subs                      full
% 11.14/2.01  --res_backward_subs                     full
% 11.14/2.01  --res_forward_subs_resolution           true
% 11.14/2.01  --res_backward_subs_resolution          true
% 11.14/2.01  --res_orphan_elimination                true
% 11.14/2.01  --res_time_limit                        2.
% 11.14/2.01  --res_out_proof                         true
% 11.14/2.01  
% 11.14/2.01  ------ Superposition Options
% 11.14/2.01  
% 11.14/2.01  --superposition_flag                    true
% 11.14/2.01  --sup_passive_queue_type                priority_queues
% 11.14/2.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.14/2.01  --sup_passive_queues_freq               [8;1;4]
% 11.14/2.01  --demod_completeness_check              fast
% 11.14/2.01  --demod_use_ground                      true
% 11.14/2.01  --sup_to_prop_solver                    passive
% 11.14/2.01  --sup_prop_simpl_new                    true
% 11.14/2.01  --sup_prop_simpl_given                  true
% 11.14/2.01  --sup_fun_splitting                     false
% 11.14/2.01  --sup_smt_interval                      50000
% 11.14/2.01  
% 11.14/2.01  ------ Superposition Simplification Setup
% 11.14/2.01  
% 11.14/2.01  --sup_indices_passive                   []
% 11.14/2.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.14/2.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.14/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.14/2.01  --sup_full_triv                         [TrivRules;PropSubs]
% 11.14/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.14/2.01  --sup_full_bw                           [BwDemod]
% 11.14/2.01  --sup_immed_triv                        [TrivRules]
% 11.14/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.14/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.14/2.01  --sup_immed_bw_main                     []
% 11.14/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.14/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 11.14/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.14/2.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.14/2.01  
% 11.14/2.01  ------ Combination Options
% 11.14/2.01  
% 11.14/2.01  --comb_res_mult                         3
% 11.14/2.01  --comb_sup_mult                         2
% 11.14/2.01  --comb_inst_mult                        10
% 11.14/2.01  
% 11.14/2.01  ------ Debug Options
% 11.14/2.01  
% 11.14/2.01  --dbg_backtrace                         false
% 11.14/2.01  --dbg_dump_prop_clauses                 false
% 11.14/2.01  --dbg_dump_prop_clauses_file            -
% 11.14/2.01  --dbg_out_stat                          false
% 11.14/2.01  
% 11.14/2.01  
% 11.14/2.01  
% 11.14/2.01  
% 11.14/2.01  ------ Proving...
% 11.14/2.01  
% 11.14/2.01  
% 11.14/2.01  % SZS status Theorem for theBenchmark.p
% 11.14/2.01  
% 11.14/2.01   Resolution empty clause
% 11.14/2.01  
% 11.14/2.01  % SZS output start CNFRefutation for theBenchmark.p
% 11.14/2.01  
% 11.14/2.01  fof(f21,axiom,(
% 11.14/2.01    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 11.14/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/2.01  
% 11.14/2.01  fof(f31,plain,(
% 11.14/2.01    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 11.14/2.01    inference(ennf_transformation,[],[f21])).
% 11.14/2.01  
% 11.14/2.01  fof(f75,plain,(
% 11.14/2.01    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 11.14/2.01    inference(cnf_transformation,[],[f31])).
% 11.14/2.01  
% 11.14/2.01  fof(f12,axiom,(
% 11.14/2.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 11.14/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/2.01  
% 11.14/2.01  fof(f66,plain,(
% 11.14/2.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 11.14/2.01    inference(cnf_transformation,[],[f12])).
% 11.14/2.01  
% 11.14/2.01  fof(f13,axiom,(
% 11.14/2.01    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 11.14/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/2.01  
% 11.14/2.01  fof(f67,plain,(
% 11.14/2.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 11.14/2.01    inference(cnf_transformation,[],[f13])).
% 11.14/2.01  
% 11.14/2.01  fof(f14,axiom,(
% 11.14/2.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.14/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/2.01  
% 11.14/2.01  fof(f68,plain,(
% 11.14/2.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.14/2.01    inference(cnf_transformation,[],[f14])).
% 11.14/2.01  
% 11.14/2.01  fof(f15,axiom,(
% 11.14/2.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 11.14/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/2.01  
% 11.14/2.01  fof(f69,plain,(
% 11.14/2.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 11.14/2.01    inference(cnf_transformation,[],[f15])).
% 11.14/2.01  
% 11.14/2.01  fof(f16,axiom,(
% 11.14/2.01    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 11.14/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/2.01  
% 11.14/2.01  fof(f70,plain,(
% 11.14/2.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 11.14/2.01    inference(cnf_transformation,[],[f16])).
% 11.14/2.01  
% 11.14/2.01  fof(f17,axiom,(
% 11.14/2.01    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 11.14/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/2.01  
% 11.14/2.01  fof(f71,plain,(
% 11.14/2.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 11.14/2.01    inference(cnf_transformation,[],[f17])).
% 11.14/2.01  
% 11.14/2.01  fof(f18,axiom,(
% 11.14/2.01    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 11.14/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/2.01  
% 11.14/2.01  fof(f72,plain,(
% 11.14/2.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 11.14/2.01    inference(cnf_transformation,[],[f18])).
% 11.14/2.01  
% 11.14/2.01  fof(f78,plain,(
% 11.14/2.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 11.14/2.01    inference(definition_unfolding,[],[f71,f72])).
% 11.14/2.01  
% 11.14/2.01  fof(f79,plain,(
% 11.14/2.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 11.14/2.01    inference(definition_unfolding,[],[f70,f78])).
% 11.14/2.01  
% 11.14/2.01  fof(f80,plain,(
% 11.14/2.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 11.14/2.01    inference(definition_unfolding,[],[f69,f79])).
% 11.14/2.01  
% 11.14/2.01  fof(f81,plain,(
% 11.14/2.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 11.14/2.01    inference(definition_unfolding,[],[f68,f80])).
% 11.14/2.01  
% 11.14/2.01  fof(f82,plain,(
% 11.14/2.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 11.14/2.01    inference(definition_unfolding,[],[f67,f81])).
% 11.14/2.01  
% 11.14/2.01  fof(f83,plain,(
% 11.14/2.01    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 11.14/2.01    inference(definition_unfolding,[],[f66,f82])).
% 11.14/2.01  
% 11.14/2.01  fof(f99,plain,(
% 11.14/2.01    ( ! [X0,X1] : (r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1) )),
% 11.14/2.01    inference(definition_unfolding,[],[f75,f83,f83])).
% 11.14/2.01  
% 11.14/2.01  fof(f9,axiom,(
% 11.14/2.01    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 11.14/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/2.01  
% 11.14/2.01  fof(f38,plain,(
% 11.14/2.01    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 11.14/2.01    inference(nnf_transformation,[],[f9])).
% 11.14/2.01  
% 11.14/2.01  fof(f55,plain,(
% 11.14/2.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 11.14/2.01    inference(cnf_transformation,[],[f38])).
% 11.14/2.01  
% 11.14/2.01  fof(f23,conjecture,(
% 11.14/2.01    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 11.14/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/2.01  
% 11.14/2.01  fof(f24,negated_conjecture,(
% 11.14/2.01    ~! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 11.14/2.01    inference(negated_conjecture,[],[f23])).
% 11.14/2.01  
% 11.14/2.01  fof(f33,plain,(
% 11.14/2.01    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 11.14/2.01    inference(ennf_transformation,[],[f24])).
% 11.14/2.01  
% 11.14/2.01  fof(f44,plain,(
% 11.14/2.01    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) => k2_tarski(sK3,sK4) != k3_tarski(k2_tarski(k1_tarski(sK3),k1_tarski(sK4)))),
% 11.14/2.01    introduced(choice_axiom,[])).
% 11.14/2.01  
% 11.14/2.01  fof(f45,plain,(
% 11.14/2.01    k2_tarski(sK3,sK4) != k3_tarski(k2_tarski(k1_tarski(sK3),k1_tarski(sK4)))),
% 11.14/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f33,f44])).
% 11.14/2.01  
% 11.14/2.01  fof(f77,plain,(
% 11.14/2.01    k2_tarski(sK3,sK4) != k3_tarski(k2_tarski(k1_tarski(sK3),k1_tarski(sK4)))),
% 11.14/2.01    inference(cnf_transformation,[],[f45])).
% 11.14/2.01  
% 11.14/2.01  fof(f101,plain,(
% 11.14/2.01    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k3_tarski(k6_enumset1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),
% 11.14/2.01    inference(definition_unfolding,[],[f77,f82,f82,f83,f83])).
% 11.14/2.01  
% 11.14/2.01  fof(f20,axiom,(
% 11.14/2.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 11.14/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/2.01  
% 11.14/2.01  fof(f74,plain,(
% 11.14/2.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 11.14/2.01    inference(cnf_transformation,[],[f20])).
% 11.14/2.01  
% 11.14/2.01  fof(f10,axiom,(
% 11.14/2.01    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 11.14/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/2.01  
% 11.14/2.01  fof(f57,plain,(
% 11.14/2.01    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 11.14/2.01    inference(cnf_transformation,[],[f10])).
% 11.14/2.01  
% 11.14/2.01  fof(f98,plain,(
% 11.14/2.01    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 11.14/2.01    inference(definition_unfolding,[],[f74,f57,f82])).
% 11.14/2.01  
% 11.14/2.01  fof(f22,axiom,(
% 11.14/2.01    ! [X0,X1] : (X0 != X1 => k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1))),
% 11.14/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/2.01  
% 11.14/2.01  fof(f32,plain,(
% 11.14/2.01    ! [X0,X1] : (k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) | X0 = X1)),
% 11.14/2.01    inference(ennf_transformation,[],[f22])).
% 11.14/2.01  
% 11.14/2.01  fof(f76,plain,(
% 11.14/2.01    ( ! [X0,X1] : (k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) | X0 = X1) )),
% 11.14/2.01    inference(cnf_transformation,[],[f32])).
% 11.14/2.01  
% 11.14/2.01  fof(f100,plain,(
% 11.14/2.01    ( ! [X0,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) | X0 = X1) )),
% 11.14/2.01    inference(definition_unfolding,[],[f76,f83,f83,f82])).
% 11.14/2.01  
% 11.14/2.01  fof(f7,axiom,(
% 11.14/2.01    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 11.14/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/2.01  
% 11.14/2.01  fof(f53,plain,(
% 11.14/2.01    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.14/2.01    inference(cnf_transformation,[],[f7])).
% 11.14/2.01  
% 11.14/2.01  fof(f8,axiom,(
% 11.14/2.01    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 11.14/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/2.01  
% 11.14/2.01  fof(f54,plain,(
% 11.14/2.01    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 11.14/2.01    inference(cnf_transformation,[],[f8])).
% 11.14/2.01  
% 11.14/2.01  fof(f1,axiom,(
% 11.14/2.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.14/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/2.01  
% 11.14/2.01  fof(f46,plain,(
% 11.14/2.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.14/2.01    inference(cnf_transformation,[],[f1])).
% 11.14/2.01  
% 11.14/2.01  fof(f6,axiom,(
% 11.14/2.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.14/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/2.01  
% 11.14/2.01  fof(f52,plain,(
% 11.14/2.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.14/2.01    inference(cnf_transformation,[],[f6])).
% 11.14/2.01  
% 11.14/2.01  fof(f85,plain,(
% 11.14/2.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 11.14/2.01    inference(definition_unfolding,[],[f46,f52,f52])).
% 11.14/2.01  
% 11.14/2.01  fof(f3,axiom,(
% 11.14/2.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 11.14/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/2.01  
% 11.14/2.01  fof(f26,plain,(
% 11.14/2.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 11.14/2.01    inference(rectify,[],[f3])).
% 11.14/2.01  
% 11.14/2.01  fof(f27,plain,(
% 11.14/2.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 11.14/2.01    inference(ennf_transformation,[],[f26])).
% 11.14/2.01  
% 11.14/2.01  fof(f34,plain,(
% 11.14/2.01    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 11.14/2.01    introduced(choice_axiom,[])).
% 11.14/2.01  
% 11.14/2.01  fof(f35,plain,(
% 11.14/2.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 11.14/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f34])).
% 11.14/2.01  
% 11.14/2.01  fof(f48,plain,(
% 11.14/2.01    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 11.14/2.01    inference(cnf_transformation,[],[f35])).
% 11.14/2.01  
% 11.14/2.01  fof(f88,plain,(
% 11.14/2.01    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 11.14/2.01    inference(definition_unfolding,[],[f48,f52])).
% 11.14/2.01  
% 11.14/2.01  fof(f49,plain,(
% 11.14/2.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 11.14/2.01    inference(cnf_transformation,[],[f35])).
% 11.14/2.01  
% 11.14/2.01  fof(f87,plain,(
% 11.14/2.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 11.14/2.01    inference(definition_unfolding,[],[f49,f52])).
% 11.14/2.01  
% 11.14/2.01  fof(f2,axiom,(
% 11.14/2.01    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 11.14/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/2.01  
% 11.14/2.01  fof(f25,plain,(
% 11.14/2.01    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 11.14/2.01    inference(rectify,[],[f2])).
% 11.14/2.01  
% 11.14/2.01  fof(f47,plain,(
% 11.14/2.01    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 11.14/2.01    inference(cnf_transformation,[],[f25])).
% 11.14/2.01  
% 11.14/2.01  fof(f86,plain,(
% 11.14/2.01    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 11.14/2.01    inference(definition_unfolding,[],[f47,f52])).
% 11.14/2.01  
% 11.14/2.01  fof(f5,axiom,(
% 11.14/2.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.14/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.14/2.01  
% 11.14/2.01  fof(f51,plain,(
% 11.14/2.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.14/2.01    inference(cnf_transformation,[],[f5])).
% 11.14/2.01  
% 11.14/2.01  fof(f84,plain,(
% 11.14/2.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 11.14/2.01    inference(definition_unfolding,[],[f51,f52])).
% 11.14/2.01  
% 11.14/2.01  cnf(c_20,plain,
% 11.14/2.01      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 11.14/2.01      | X1 = X0 ),
% 11.14/2.01      inference(cnf_transformation,[],[f99]) ).
% 11.14/2.01  
% 11.14/2.01  cnf(c_1247,plain,
% 11.14/2.01      ( X0 = X1
% 11.14/2.01      | r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
% 11.14/2.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.14/2.01  
% 11.14/2.01  cnf(c_9,plain,
% 11.14/2.01      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 11.14/2.01      inference(cnf_transformation,[],[f55]) ).
% 11.14/2.01  
% 11.14/2.01  cnf(c_1257,plain,
% 11.14/2.01      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 11.14/2.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.14/2.01  
% 11.14/2.01  cnf(c_1863,plain,
% 11.14/2.01      ( X0 = X1
% 11.14/2.01      | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 11.14/2.01      inference(superposition,[status(thm)],[c_1247,c_1257]) ).
% 11.14/2.01  
% 11.14/2.01  cnf(c_22,negated_conjecture,
% 11.14/2.01      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k3_tarski(k6_enumset1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) ),
% 11.14/2.01      inference(cnf_transformation,[],[f101]) ).
% 11.14/2.01  
% 11.14/2.01  cnf(c_19,plain,
% 11.14/2.01      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 11.14/2.01      inference(cnf_transformation,[],[f98]) ).
% 11.14/2.01  
% 11.14/2.01  cnf(c_1349,plain,
% 11.14/2.01      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) ),
% 11.14/2.01      inference(demodulation,[status(thm)],[c_22,c_19]) ).
% 11.14/2.01  
% 11.14/2.01  cnf(c_11815,plain,
% 11.14/2.01      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 11.14/2.01      | sK4 = sK3 ),
% 11.14/2.01      inference(superposition,[status(thm)],[c_1863,c_1349]) ).
% 11.14/2.01  
% 11.14/2.01  cnf(c_21,plain,
% 11.14/2.01      ( X0 = X1
% 11.14/2.01      | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
% 11.14/2.01      inference(cnf_transformation,[],[f100]) ).
% 11.14/2.01  
% 11.14/2.01  cnf(c_1707,plain,
% 11.14/2.01      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4)
% 11.14/2.01      | sK4 = X0 ),
% 11.14/2.01      inference(instantiation,[status(thm)],[c_21]) ).
% 11.14/2.01  
% 11.14/2.01  cnf(c_1713,plain,
% 11.14/2.01      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 11.14/2.01      | sK4 = sK3 ),
% 11.14/2.01      inference(instantiation,[status(thm)],[c_1707]) ).
% 11.14/2.01  
% 11.14/2.01  cnf(c_14557,plain,
% 11.14/2.01      ( sK4 = sK3 ),
% 11.14/2.01      inference(global_propositional_subsumption,
% 11.14/2.01                [status(thm)],
% 11.14/2.01                [c_11815,c_1713]) ).
% 11.14/2.01  
% 11.14/2.01  cnf(c_14560,plain,
% 11.14/2.01      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 11.14/2.01      inference(demodulation,[status(thm)],[c_14557,c_1349]) ).
% 11.14/2.01  
% 11.14/2.01  cnf(c_6,plain,
% 11.14/2.01      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.14/2.01      inference(cnf_transformation,[],[f53]) ).
% 11.14/2.01  
% 11.14/2.01  cnf(c_7,plain,
% 11.14/2.01      ( r1_xboole_0(X0,k1_xboole_0) ),
% 11.14/2.01      inference(cnf_transformation,[],[f54]) ).
% 11.14/2.01  
% 11.14/2.01  cnf(c_1259,plain,
% 11.14/2.01      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 11.14/2.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.14/2.01  
% 11.14/2.01  cnf(c_1,plain,
% 11.14/2.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.14/2.01      inference(cnf_transformation,[],[f85]) ).
% 11.14/2.01  
% 11.14/2.01  cnf(c_4,plain,
% 11.14/2.01      ( r2_hidden(sK0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
% 11.14/2.01      | r1_xboole_0(X0,X1) ),
% 11.14/2.01      inference(cnf_transformation,[],[f88]) ).
% 11.14/2.01  
% 11.14/2.01  cnf(c_1261,plain,
% 11.14/2.01      ( r2_hidden(sK0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = iProver_top
% 11.14/2.01      | r1_xboole_0(X0,X1) = iProver_top ),
% 11.14/2.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.14/2.01  
% 11.14/2.01  cnf(c_4196,plain,
% 11.14/2.01      ( r2_hidden(sK0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = iProver_top
% 11.14/2.01      | r1_xboole_0(X0,X1) = iProver_top ),
% 11.14/2.01      inference(superposition,[status(thm)],[c_1,c_1261]) ).
% 11.14/2.01  
% 11.14/2.01  cnf(c_3,plain,
% 11.14/2.01      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 11.14/2.01      | ~ r1_xboole_0(X1,X2) ),
% 11.14/2.01      inference(cnf_transformation,[],[f87]) ).
% 11.14/2.01  
% 11.14/2.01  cnf(c_1262,plain,
% 11.14/2.01      ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
% 11.14/2.01      | r1_xboole_0(X1,X2) != iProver_top ),
% 11.14/2.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.14/2.01  
% 11.14/2.01  cnf(c_5920,plain,
% 11.14/2.01      ( r1_xboole_0(X0,X1) != iProver_top | r1_xboole_0(X1,X0) = iProver_top ),
% 11.14/2.01      inference(superposition,[status(thm)],[c_4196,c_1262]) ).
% 11.14/2.01  
% 11.14/2.01  cnf(c_6153,plain,
% 11.14/2.01      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 11.14/2.01      inference(superposition,[status(thm)],[c_1259,c_5920]) ).
% 11.14/2.01  
% 11.14/2.01  cnf(c_6205,plain,
% 11.14/2.01      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.14/2.01      inference(superposition,[status(thm)],[c_6153,c_1257]) ).
% 11.14/2.01  
% 11.14/2.01  cnf(c_1862,plain,
% 11.14/2.01      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.14/2.01      inference(superposition,[status(thm)],[c_1259,c_1257]) ).
% 11.14/2.01  
% 11.14/2.01  cnf(c_1874,plain,
% 11.14/2.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 11.14/2.01      inference(superposition,[status(thm)],[c_1862,c_1]) ).
% 11.14/2.01  
% 11.14/2.01  cnf(c_6480,plain,
% 11.14/2.01      ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 11.14/2.01      inference(demodulation,[status(thm)],[c_6205,c_1874]) ).
% 11.14/2.01  
% 11.14/2.01  cnf(c_2,plain,
% 11.14/2.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 11.14/2.01      inference(cnf_transformation,[],[f86]) ).
% 11.14/2.01  
% 11.14/2.01  cnf(c_0,plain,
% 11.14/2.01      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 11.14/2.01      inference(cnf_transformation,[],[f84]) ).
% 11.14/2.01  
% 11.14/2.01  cnf(c_1433,plain,
% 11.14/2.01      ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
% 11.14/2.01      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 11.14/2.01  
% 11.14/2.01  cnf(c_1443,plain,
% 11.14/2.01      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 11.14/2.01      inference(superposition,[status(thm)],[c_6,c_1433]) ).
% 11.14/2.01  
% 11.14/2.01  cnf(c_6496,plain,
% 11.14/2.01      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.14/2.01      inference(light_normalisation,[status(thm)],[c_6480,c_1443]) ).
% 11.14/2.01  
% 11.14/2.01  cnf(c_14561,plain,
% 11.14/2.01      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 11.14/2.01      inference(demodulation,[status(thm)],[c_14560,c_6,c_6496]) ).
% 11.14/2.01  
% 11.14/2.01  cnf(c_14562,plain,
% 11.14/2.01      ( $false ),
% 11.14/2.01      inference(equality_resolution_simp,[status(thm)],[c_14561]) ).
% 11.14/2.01  
% 11.14/2.01  
% 11.14/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 11.14/2.01  
% 11.14/2.01  ------                               Statistics
% 11.14/2.01  
% 11.14/2.01  ------ General
% 11.14/2.01  
% 11.14/2.01  abstr_ref_over_cycles:                  0
% 11.14/2.01  abstr_ref_under_cycles:                 0
% 11.14/2.01  gc_basic_clause_elim:                   0
% 11.14/2.01  forced_gc_time:                         0
% 11.14/2.01  parsing_time:                           0.01
% 11.14/2.01  unif_index_cands_time:                  0.
% 11.14/2.01  unif_index_add_time:                    0.
% 11.14/2.01  orderings_time:                         0.
% 11.14/2.01  out_proof_time:                         0.01
% 11.14/2.01  total_time:                             1.049
% 11.14/2.01  num_of_symbols:                         43
% 11.14/2.01  num_of_terms:                           18118
% 11.14/2.01  
% 11.14/2.01  ------ Preprocessing
% 11.14/2.01  
% 11.14/2.01  num_of_splits:                          0
% 11.14/2.01  num_of_split_atoms:                     0
% 11.14/2.01  num_of_reused_defs:                     0
% 11.14/2.01  num_eq_ax_congr_red:                    16
% 11.14/2.01  num_of_sem_filtered_clauses:            1
% 11.14/2.01  num_of_subtypes:                        0
% 11.14/2.01  monotx_restored_types:                  0
% 11.14/2.01  sat_num_of_epr_types:                   0
% 11.14/2.01  sat_num_of_non_cyclic_types:            0
% 11.14/2.01  sat_guarded_non_collapsed_types:        0
% 11.14/2.01  num_pure_diseq_elim:                    0
% 11.14/2.01  simp_replaced_by:                       0
% 11.14/2.01  res_preprocessed:                       86
% 11.14/2.01  prep_upred:                             0
% 11.14/2.01  prep_unflattend:                        55
% 11.14/2.01  smt_new_axioms:                         0
% 11.14/2.01  pred_elim_cands:                        2
% 11.14/2.01  pred_elim:                              0
% 11.14/2.01  pred_elim_cl:                           0
% 11.14/2.01  pred_elim_cycles:                       2
% 11.14/2.01  merged_defs:                            6
% 11.14/2.01  merged_defs_ncl:                        0
% 11.14/2.01  bin_hyper_res:                          6
% 11.14/2.01  prep_cycles:                            3
% 11.14/2.01  pred_elim_time:                         0.01
% 11.14/2.01  splitting_time:                         0.
% 11.14/2.01  sem_filter_time:                        0.
% 11.14/2.01  monotx_time:                            0.
% 11.14/2.01  subtype_inf_time:                       0.
% 11.14/2.01  
% 11.14/2.01  ------ Problem properties
% 11.14/2.01  
% 11.14/2.01  clauses:                                23
% 11.14/2.01  conjectures:                            1
% 11.14/2.01  epr:                                    1
% 11.14/2.01  horn:                                   17
% 11.14/2.01  ground:                                 1
% 11.14/2.01  unary:                                  10
% 11.14/2.01  binary:                                 8
% 11.14/2.01  lits:                                   44
% 11.14/2.01  lits_eq:                                26
% 11.14/2.01  fd_pure:                                0
% 11.14/2.01  fd_pseudo:                              0
% 11.14/2.01  fd_cond:                                1
% 11.14/2.01  fd_pseudo_cond:                         6
% 11.14/2.01  ac_symbols:                             0
% 11.14/2.01  
% 11.14/2.01  ------ Propositional Solver
% 11.14/2.01  
% 11.14/2.01  prop_solver_calls:                      24
% 11.14/2.01  prop_fast_solver_calls:                 659
% 11.14/2.01  smt_solver_calls:                       0
% 11.14/2.01  smt_fast_solver_calls:                  0
% 11.14/2.01  prop_num_of_clauses:                    4666
% 11.14/2.01  prop_preprocess_simplified:             9188
% 11.14/2.01  prop_fo_subsumed:                       1
% 11.14/2.01  prop_solver_time:                       0.
% 11.14/2.01  smt_solver_time:                        0.
% 11.14/2.01  smt_fast_solver_time:                   0.
% 11.14/2.01  prop_fast_solver_time:                  0.
% 11.14/2.01  prop_unsat_core_time:                   0.
% 11.14/2.01  
% 11.14/2.01  ------ QBF
% 11.14/2.01  
% 11.14/2.01  qbf_q_res:                              0
% 11.14/2.01  qbf_num_tautologies:                    0
% 11.14/2.01  qbf_prep_cycles:                        0
% 11.14/2.01  
% 11.14/2.01  ------ BMC1
% 11.14/2.01  
% 11.14/2.01  bmc1_current_bound:                     -1
% 11.14/2.01  bmc1_last_solved_bound:                 -1
% 11.14/2.01  bmc1_unsat_core_size:                   -1
% 11.14/2.01  bmc1_unsat_core_parents_size:           -1
% 11.14/2.01  bmc1_merge_next_fun:                    0
% 11.14/2.01  bmc1_unsat_core_clauses_time:           0.
% 11.14/2.01  
% 11.14/2.01  ------ Instantiation
% 11.14/2.01  
% 11.14/2.01  inst_num_of_clauses:                    1215
% 11.14/2.01  inst_num_in_passive:                    330
% 11.14/2.01  inst_num_in_active:                     347
% 11.14/2.01  inst_num_in_unprocessed:                538
% 11.14/2.01  inst_num_of_loops:                      440
% 11.14/2.01  inst_num_of_learning_restarts:          0
% 11.14/2.01  inst_num_moves_active_passive:          91
% 11.14/2.01  inst_lit_activity:                      0
% 11.14/2.01  inst_lit_activity_moves:                0
% 11.14/2.01  inst_num_tautologies:                   0
% 11.14/2.01  inst_num_prop_implied:                  0
% 11.14/2.01  inst_num_existing_simplified:           0
% 11.14/2.01  inst_num_eq_res_simplified:             0
% 11.14/2.01  inst_num_child_elim:                    0
% 11.14/2.01  inst_num_of_dismatching_blockings:      1131
% 11.14/2.01  inst_num_of_non_proper_insts:           1520
% 11.14/2.01  inst_num_of_duplicates:                 0
% 11.14/2.01  inst_inst_num_from_inst_to_res:         0
% 11.14/2.01  inst_dismatching_checking_time:         0.
% 11.14/2.01  
% 11.14/2.01  ------ Resolution
% 11.14/2.01  
% 11.14/2.01  res_num_of_clauses:                     0
% 11.14/2.01  res_num_in_passive:                     0
% 11.14/2.01  res_num_in_active:                      0
% 11.14/2.01  res_num_of_loops:                       89
% 11.14/2.01  res_forward_subset_subsumed:            113
% 11.14/2.01  res_backward_subset_subsumed:           0
% 11.14/2.01  res_forward_subsumed:                   0
% 11.14/2.01  res_backward_subsumed:                  0
% 11.14/2.01  res_forward_subsumption_resolution:     1
% 11.14/2.01  res_backward_subsumption_resolution:    0
% 11.14/2.01  res_clause_to_clause_subsumption:       6100
% 11.14/2.01  res_orphan_elimination:                 0
% 11.14/2.01  res_tautology_del:                      58
% 11.14/2.01  res_num_eq_res_simplified:              0
% 11.14/2.01  res_num_sel_changes:                    0
% 11.14/2.01  res_moves_from_active_to_pass:          0
% 11.14/2.01  
% 11.14/2.01  ------ Superposition
% 11.14/2.01  
% 11.14/2.01  sup_time_total:                         0.
% 11.14/2.01  sup_time_generating:                    0.
% 11.14/2.01  sup_time_sim_full:                      0.
% 11.14/2.01  sup_time_sim_immed:                     0.
% 11.14/2.01  
% 11.14/2.01  sup_num_of_clauses:                     472
% 11.14/2.01  sup_num_in_active:                      60
% 11.14/2.01  sup_num_in_passive:                     412
% 11.14/2.01  sup_num_of_loops:                       87
% 11.14/2.01  sup_fw_superposition:                   825
% 11.14/2.01  sup_bw_superposition:                   667
% 11.14/2.01  sup_immediate_simplified:               695
% 11.14/2.01  sup_given_eliminated:                   0
% 11.14/2.01  comparisons_done:                       0
% 11.14/2.01  comparisons_avoided:                    9
% 11.14/2.01  
% 11.14/2.01  ------ Simplifications
% 11.14/2.01  
% 11.14/2.01  
% 11.14/2.01  sim_fw_subset_subsumed:                 18
% 11.14/2.01  sim_bw_subset_subsumed:                 1
% 11.14/2.01  sim_fw_subsumed:                        134
% 11.14/2.01  sim_bw_subsumed:                        5
% 11.14/2.01  sim_fw_subsumption_res:                 1
% 11.14/2.01  sim_bw_subsumption_res:                 0
% 11.14/2.01  sim_tautology_del:                      11
% 11.14/2.01  sim_eq_tautology_del:                   124
% 11.14/2.01  sim_eq_res_simp:                        15
% 11.14/2.01  sim_fw_demodulated:                     182
% 11.14/2.01  sim_bw_demodulated:                     58
% 11.14/2.01  sim_light_normalised:                   415
% 11.14/2.01  sim_joinable_taut:                      0
% 11.14/2.01  sim_joinable_simp:                      0
% 11.14/2.01  sim_ac_normalised:                      0
% 11.14/2.01  sim_smt_subsumption:                    0
% 11.14/2.01  
%------------------------------------------------------------------------------
