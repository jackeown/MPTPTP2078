%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:12 EST 2020

% Result     : Theorem 15.02s
% Output     : CNFRefutation 15.02s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 328 expanded)
%              Number of clauses        :   41 (  78 expanded)
%              Number of leaves         :   18 (  92 expanded)
%              Depth                    :   17
%              Number of atoms          :  125 ( 364 expanded)
%              Number of equality atoms :  105 ( 344 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f16])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f39,f46])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f38,f47])).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f37,f48])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f36,f49])).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f35,f50])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f33,f51,f51])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f51,f51])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f31,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)
      & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)
        & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
   => ( k4_xboole_0(k1_tarski(sK0),sK1) != k1_tarski(sK0)
      & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( k4_xboole_0(k1_tarski(sK0),sK1) != k1_tarski(sK0)
    & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f26])).

fof(f45,plain,(
    k4_xboole_0(k1_tarski(sK0),sK1) != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f54,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f45,f33,f51,f51])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f44,plain,(
    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f55,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_xboole_0 ),
    inference(definition_unfolding,[],[f44,f33,f51])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_151,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_152,plain,
    ( k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_924,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(superposition,[status(thm)],[c_151,c_152])).

cnf(c_3,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_5,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_372,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(k5_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_3,c_5])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1050,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_372,c_1])).

cnf(c_368,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_3,c_5])).

cnf(c_1699,plain,
    ( k3_xboole_0(k5_xboole_0(X0,X1),X0) = k3_xboole_0(k5_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_1050,c_368])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_3973,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1699,c_0])).

cnf(c_572,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(k5_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_0,c_368])).

cnf(c_5092,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_3973,c_572])).

cnf(c_44456,plain,
    ( k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(demodulation,[status(thm)],[c_924,c_5092])).

cnf(c_8,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_199,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(demodulation,[status(thm)],[c_0,c_8])).

cnf(c_566,plain,
    ( k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(demodulation,[status(thm)],[c_368,c_199])).

cnf(c_686,plain,
    ( k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[status(thm)],[c_0,c_566])).

cnf(c_748,plain,
    ( k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[status(thm)],[c_1,c_686])).

cnf(c_44525,plain,
    ( k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[status(thm)],[c_44456,c_748])).

cnf(c_1689,plain,
    ( k3_xboole_0(k5_xboole_0(X0,X1),X1) = k3_xboole_0(k5_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_368,c_1050])).

cnf(c_3776,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,X1)) = k3_xboole_0(k5_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_1689,c_0])).

cnf(c_4937,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_3776,c_1050])).

cnf(c_45369,plain,
    ( k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_44525,c_4937])).

cnf(c_574,plain,
    ( k3_xboole_0(k5_xboole_0(X0,X0),X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_3,c_368])).

cnf(c_1021,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,X0)) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_574,c_0])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_4,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_64,plain,
    ( k5_xboole_0(X0,X1) != X2
    | k3_xboole_0(X0,X1) != X3
    | k3_xboole_0(X3,X2) = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_4])).

cnf(c_65,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_64])).

cnf(c_306,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3,c_65])).

cnf(c_1026,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1021,c_306])).

cnf(c_45404,plain,
    ( k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_45369,c_1026])).

cnf(c_9,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_200,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_0,c_9])).

cnf(c_567,plain,
    ( k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_368,c_200])).

cnf(c_600,plain,
    ( k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_567])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_45404,c_600])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:35:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 15.02/2.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.02/2.50  
% 15.02/2.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.02/2.50  
% 15.02/2.50  ------  iProver source info
% 15.02/2.50  
% 15.02/2.50  git: date: 2020-06-30 10:37:57 +0100
% 15.02/2.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.02/2.50  git: non_committed_changes: false
% 15.02/2.50  git: last_make_outside_of_git: false
% 15.02/2.50  
% 15.02/2.50  ------ 
% 15.02/2.50  
% 15.02/2.50  ------ Input Options
% 15.02/2.50  
% 15.02/2.50  --out_options                           all
% 15.02/2.50  --tptp_safe_out                         true
% 15.02/2.50  --problem_path                          ""
% 15.02/2.50  --include_path                          ""
% 15.02/2.50  --clausifier                            res/vclausify_rel
% 15.02/2.50  --clausifier_options                    --mode clausify
% 15.02/2.50  --stdin                                 false
% 15.02/2.50  --stats_out                             all
% 15.02/2.50  
% 15.02/2.50  ------ General Options
% 15.02/2.50  
% 15.02/2.50  --fof                                   false
% 15.02/2.50  --time_out_real                         305.
% 15.02/2.50  --time_out_virtual                      -1.
% 15.02/2.50  --symbol_type_check                     false
% 15.02/2.50  --clausify_out                          false
% 15.02/2.50  --sig_cnt_out                           false
% 15.02/2.50  --trig_cnt_out                          false
% 15.02/2.50  --trig_cnt_out_tolerance                1.
% 15.02/2.50  --trig_cnt_out_sk_spl                   false
% 15.02/2.50  --abstr_cl_out                          false
% 15.02/2.50  
% 15.02/2.50  ------ Global Options
% 15.02/2.50  
% 15.02/2.50  --schedule                              default
% 15.02/2.50  --add_important_lit                     false
% 15.02/2.50  --prop_solver_per_cl                    1000
% 15.02/2.50  --min_unsat_core                        false
% 15.02/2.50  --soft_assumptions                      false
% 15.02/2.50  --soft_lemma_size                       3
% 15.02/2.50  --prop_impl_unit_size                   0
% 15.02/2.50  --prop_impl_unit                        []
% 15.02/2.50  --share_sel_clauses                     true
% 15.02/2.50  --reset_solvers                         false
% 15.02/2.50  --bc_imp_inh                            [conj_cone]
% 15.02/2.50  --conj_cone_tolerance                   3.
% 15.02/2.50  --extra_neg_conj                        none
% 15.02/2.50  --large_theory_mode                     true
% 15.02/2.50  --prolific_symb_bound                   200
% 15.02/2.50  --lt_threshold                          2000
% 15.02/2.50  --clause_weak_htbl                      true
% 15.02/2.50  --gc_record_bc_elim                     false
% 15.02/2.50  
% 15.02/2.50  ------ Preprocessing Options
% 15.02/2.50  
% 15.02/2.50  --preprocessing_flag                    true
% 15.02/2.50  --time_out_prep_mult                    0.1
% 15.02/2.50  --splitting_mode                        input
% 15.02/2.50  --splitting_grd                         true
% 15.02/2.50  --splitting_cvd                         false
% 15.02/2.50  --splitting_cvd_svl                     false
% 15.02/2.50  --splitting_nvd                         32
% 15.02/2.50  --sub_typing                            true
% 15.02/2.50  --prep_gs_sim                           true
% 15.02/2.50  --prep_unflatten                        true
% 15.02/2.50  --prep_res_sim                          true
% 15.02/2.50  --prep_upred                            true
% 15.02/2.50  --prep_sem_filter                       exhaustive
% 15.02/2.50  --prep_sem_filter_out                   false
% 15.02/2.50  --pred_elim                             true
% 15.02/2.50  --res_sim_input                         true
% 15.02/2.50  --eq_ax_congr_red                       true
% 15.02/2.50  --pure_diseq_elim                       true
% 15.02/2.50  --brand_transform                       false
% 15.02/2.50  --non_eq_to_eq                          false
% 15.02/2.50  --prep_def_merge                        true
% 15.02/2.50  --prep_def_merge_prop_impl              false
% 15.02/2.50  --prep_def_merge_mbd                    true
% 15.02/2.50  --prep_def_merge_tr_red                 false
% 15.02/2.50  --prep_def_merge_tr_cl                  false
% 15.02/2.50  --smt_preprocessing                     true
% 15.02/2.50  --smt_ac_axioms                         fast
% 15.02/2.50  --preprocessed_out                      false
% 15.02/2.50  --preprocessed_stats                    false
% 15.02/2.50  
% 15.02/2.50  ------ Abstraction refinement Options
% 15.02/2.50  
% 15.02/2.50  --abstr_ref                             []
% 15.02/2.50  --abstr_ref_prep                        false
% 15.02/2.50  --abstr_ref_until_sat                   false
% 15.02/2.50  --abstr_ref_sig_restrict                funpre
% 15.02/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 15.02/2.50  --abstr_ref_under                       []
% 15.02/2.50  
% 15.02/2.50  ------ SAT Options
% 15.02/2.50  
% 15.02/2.50  --sat_mode                              false
% 15.02/2.50  --sat_fm_restart_options                ""
% 15.02/2.50  --sat_gr_def                            false
% 15.02/2.50  --sat_epr_types                         true
% 15.02/2.50  --sat_non_cyclic_types                  false
% 15.02/2.50  --sat_finite_models                     false
% 15.02/2.50  --sat_fm_lemmas                         false
% 15.02/2.50  --sat_fm_prep                           false
% 15.02/2.50  --sat_fm_uc_incr                        true
% 15.02/2.50  --sat_out_model                         small
% 15.02/2.50  --sat_out_clauses                       false
% 15.02/2.50  
% 15.02/2.50  ------ QBF Options
% 15.02/2.50  
% 15.02/2.50  --qbf_mode                              false
% 15.02/2.50  --qbf_elim_univ                         false
% 15.02/2.50  --qbf_dom_inst                          none
% 15.02/2.50  --qbf_dom_pre_inst                      false
% 15.02/2.50  --qbf_sk_in                             false
% 15.02/2.50  --qbf_pred_elim                         true
% 15.02/2.50  --qbf_split                             512
% 15.02/2.50  
% 15.02/2.50  ------ BMC1 Options
% 15.02/2.50  
% 15.02/2.50  --bmc1_incremental                      false
% 15.02/2.50  --bmc1_axioms                           reachable_all
% 15.02/2.50  --bmc1_min_bound                        0
% 15.02/2.50  --bmc1_max_bound                        -1
% 15.02/2.50  --bmc1_max_bound_default                -1
% 15.02/2.50  --bmc1_symbol_reachability              true
% 15.02/2.50  --bmc1_property_lemmas                  false
% 15.02/2.50  --bmc1_k_induction                      false
% 15.02/2.50  --bmc1_non_equiv_states                 false
% 15.02/2.50  --bmc1_deadlock                         false
% 15.02/2.50  --bmc1_ucm                              false
% 15.02/2.50  --bmc1_add_unsat_core                   none
% 15.02/2.50  --bmc1_unsat_core_children              false
% 15.02/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 15.02/2.50  --bmc1_out_stat                         full
% 15.02/2.50  --bmc1_ground_init                      false
% 15.02/2.50  --bmc1_pre_inst_next_state              false
% 15.02/2.50  --bmc1_pre_inst_state                   false
% 15.02/2.50  --bmc1_pre_inst_reach_state             false
% 15.02/2.50  --bmc1_out_unsat_core                   false
% 15.02/2.50  --bmc1_aig_witness_out                  false
% 15.02/2.50  --bmc1_verbose                          false
% 15.02/2.50  --bmc1_dump_clauses_tptp                false
% 15.02/2.50  --bmc1_dump_unsat_core_tptp             false
% 15.02/2.50  --bmc1_dump_file                        -
% 15.02/2.50  --bmc1_ucm_expand_uc_limit              128
% 15.02/2.50  --bmc1_ucm_n_expand_iterations          6
% 15.02/2.50  --bmc1_ucm_extend_mode                  1
% 15.02/2.50  --bmc1_ucm_init_mode                    2
% 15.02/2.50  --bmc1_ucm_cone_mode                    none
% 15.02/2.50  --bmc1_ucm_reduced_relation_type        0
% 15.02/2.50  --bmc1_ucm_relax_model                  4
% 15.02/2.50  --bmc1_ucm_full_tr_after_sat            true
% 15.02/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 15.02/2.50  --bmc1_ucm_layered_model                none
% 15.02/2.50  --bmc1_ucm_max_lemma_size               10
% 15.02/2.50  
% 15.02/2.50  ------ AIG Options
% 15.02/2.50  
% 15.02/2.50  --aig_mode                              false
% 15.02/2.50  
% 15.02/2.50  ------ Instantiation Options
% 15.02/2.50  
% 15.02/2.50  --instantiation_flag                    true
% 15.02/2.50  --inst_sos_flag                         false
% 15.02/2.50  --inst_sos_phase                        true
% 15.02/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.02/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.02/2.50  --inst_lit_sel_side                     num_symb
% 15.02/2.50  --inst_solver_per_active                1400
% 15.02/2.50  --inst_solver_calls_frac                1.
% 15.02/2.50  --inst_passive_queue_type               priority_queues
% 15.02/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.02/2.50  --inst_passive_queues_freq              [25;2]
% 15.02/2.50  --inst_dismatching                      true
% 15.02/2.50  --inst_eager_unprocessed_to_passive     true
% 15.02/2.50  --inst_prop_sim_given                   true
% 15.02/2.50  --inst_prop_sim_new                     false
% 15.02/2.50  --inst_subs_new                         false
% 15.02/2.50  --inst_eq_res_simp                      false
% 15.02/2.50  --inst_subs_given                       false
% 15.02/2.50  --inst_orphan_elimination               true
% 15.02/2.50  --inst_learning_loop_flag               true
% 15.02/2.50  --inst_learning_start                   3000
% 15.02/2.50  --inst_learning_factor                  2
% 15.02/2.50  --inst_start_prop_sim_after_learn       3
% 15.02/2.50  --inst_sel_renew                        solver
% 15.02/2.50  --inst_lit_activity_flag                true
% 15.02/2.50  --inst_restr_to_given                   false
% 15.02/2.50  --inst_activity_threshold               500
% 15.02/2.50  --inst_out_proof                        true
% 15.02/2.50  
% 15.02/2.50  ------ Resolution Options
% 15.02/2.50  
% 15.02/2.50  --resolution_flag                       true
% 15.02/2.50  --res_lit_sel                           adaptive
% 15.02/2.50  --res_lit_sel_side                      none
% 15.02/2.50  --res_ordering                          kbo
% 15.02/2.50  --res_to_prop_solver                    active
% 15.02/2.50  --res_prop_simpl_new                    false
% 15.02/2.50  --res_prop_simpl_given                  true
% 15.02/2.50  --res_passive_queue_type                priority_queues
% 15.02/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.02/2.50  --res_passive_queues_freq               [15;5]
% 15.02/2.50  --res_forward_subs                      full
% 15.02/2.50  --res_backward_subs                     full
% 15.02/2.50  --res_forward_subs_resolution           true
% 15.02/2.50  --res_backward_subs_resolution          true
% 15.02/2.50  --res_orphan_elimination                true
% 15.02/2.50  --res_time_limit                        2.
% 15.02/2.50  --res_out_proof                         true
% 15.02/2.50  
% 15.02/2.50  ------ Superposition Options
% 15.02/2.50  
% 15.02/2.50  --superposition_flag                    true
% 15.02/2.50  --sup_passive_queue_type                priority_queues
% 15.02/2.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.02/2.50  --sup_passive_queues_freq               [8;1;4]
% 15.02/2.50  --demod_completeness_check              fast
% 15.02/2.50  --demod_use_ground                      true
% 15.02/2.50  --sup_to_prop_solver                    passive
% 15.02/2.50  --sup_prop_simpl_new                    true
% 15.02/2.50  --sup_prop_simpl_given                  true
% 15.02/2.50  --sup_fun_splitting                     false
% 15.02/2.50  --sup_smt_interval                      50000
% 15.02/2.50  
% 15.02/2.50  ------ Superposition Simplification Setup
% 15.02/2.50  
% 15.02/2.50  --sup_indices_passive                   []
% 15.02/2.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.02/2.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.02/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.02/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 15.02/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.02/2.50  --sup_full_bw                           [BwDemod]
% 15.02/2.50  --sup_immed_triv                        [TrivRules]
% 15.02/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.02/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.02/2.50  --sup_immed_bw_main                     []
% 15.02/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.02/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 15.02/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.02/2.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.02/2.50  
% 15.02/2.50  ------ Combination Options
% 15.02/2.50  
% 15.02/2.50  --comb_res_mult                         3
% 15.02/2.50  --comb_sup_mult                         2
% 15.02/2.50  --comb_inst_mult                        10
% 15.02/2.50  
% 15.02/2.50  ------ Debug Options
% 15.02/2.50  
% 15.02/2.50  --dbg_backtrace                         false
% 15.02/2.50  --dbg_dump_prop_clauses                 false
% 15.02/2.50  --dbg_dump_prop_clauses_file            -
% 15.02/2.50  --dbg_out_stat                          false
% 15.02/2.50  ------ Parsing...
% 15.02/2.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.02/2.50  
% 15.02/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 15.02/2.50  
% 15.02/2.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.02/2.50  
% 15.02/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.02/2.50  ------ Proving...
% 15.02/2.50  ------ Problem Properties 
% 15.02/2.50  
% 15.02/2.50  
% 15.02/2.50  clauses                                 9
% 15.02/2.50  conjectures                             2
% 15.02/2.50  EPR                                     0
% 15.02/2.50  Horn                                    8
% 15.02/2.50  unary                                   7
% 15.02/2.50  binary                                  2
% 15.02/2.50  lits                                    11
% 15.02/2.50  lits eq                                 9
% 15.02/2.50  fd_pure                                 0
% 15.02/2.50  fd_pseudo                               0
% 15.02/2.50  fd_cond                                 0
% 15.02/2.50  fd_pseudo_cond                          0
% 15.02/2.50  AC symbols                              0
% 15.02/2.50  
% 15.02/2.50  ------ Schedule dynamic 5 is on 
% 15.02/2.50  
% 15.02/2.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.02/2.50  
% 15.02/2.50  
% 15.02/2.50  ------ 
% 15.02/2.50  Current options:
% 15.02/2.50  ------ 
% 15.02/2.50  
% 15.02/2.50  ------ Input Options
% 15.02/2.50  
% 15.02/2.50  --out_options                           all
% 15.02/2.50  --tptp_safe_out                         true
% 15.02/2.50  --problem_path                          ""
% 15.02/2.50  --include_path                          ""
% 15.02/2.50  --clausifier                            res/vclausify_rel
% 15.02/2.50  --clausifier_options                    --mode clausify
% 15.02/2.50  --stdin                                 false
% 15.02/2.50  --stats_out                             all
% 15.02/2.50  
% 15.02/2.50  ------ General Options
% 15.02/2.50  
% 15.02/2.50  --fof                                   false
% 15.02/2.50  --time_out_real                         305.
% 15.02/2.50  --time_out_virtual                      -1.
% 15.02/2.50  --symbol_type_check                     false
% 15.02/2.50  --clausify_out                          false
% 15.02/2.50  --sig_cnt_out                           false
% 15.02/2.50  --trig_cnt_out                          false
% 15.02/2.50  --trig_cnt_out_tolerance                1.
% 15.02/2.50  --trig_cnt_out_sk_spl                   false
% 15.02/2.50  --abstr_cl_out                          false
% 15.02/2.50  
% 15.02/2.50  ------ Global Options
% 15.02/2.50  
% 15.02/2.50  --schedule                              default
% 15.02/2.50  --add_important_lit                     false
% 15.02/2.50  --prop_solver_per_cl                    1000
% 15.02/2.50  --min_unsat_core                        false
% 15.02/2.50  --soft_assumptions                      false
% 15.02/2.50  --soft_lemma_size                       3
% 15.02/2.50  --prop_impl_unit_size                   0
% 15.02/2.50  --prop_impl_unit                        []
% 15.02/2.50  --share_sel_clauses                     true
% 15.02/2.50  --reset_solvers                         false
% 15.02/2.50  --bc_imp_inh                            [conj_cone]
% 15.02/2.50  --conj_cone_tolerance                   3.
% 15.02/2.50  --extra_neg_conj                        none
% 15.02/2.50  --large_theory_mode                     true
% 15.02/2.50  --prolific_symb_bound                   200
% 15.02/2.50  --lt_threshold                          2000
% 15.02/2.50  --clause_weak_htbl                      true
% 15.02/2.50  --gc_record_bc_elim                     false
% 15.02/2.50  
% 15.02/2.50  ------ Preprocessing Options
% 15.02/2.50  
% 15.02/2.50  --preprocessing_flag                    true
% 15.02/2.50  --time_out_prep_mult                    0.1
% 15.02/2.50  --splitting_mode                        input
% 15.02/2.50  --splitting_grd                         true
% 15.02/2.50  --splitting_cvd                         false
% 15.02/2.50  --splitting_cvd_svl                     false
% 15.02/2.50  --splitting_nvd                         32
% 15.02/2.50  --sub_typing                            true
% 15.02/2.50  --prep_gs_sim                           true
% 15.02/2.50  --prep_unflatten                        true
% 15.02/2.50  --prep_res_sim                          true
% 15.02/2.50  --prep_upred                            true
% 15.02/2.50  --prep_sem_filter                       exhaustive
% 15.02/2.50  --prep_sem_filter_out                   false
% 15.02/2.50  --pred_elim                             true
% 15.02/2.50  --res_sim_input                         true
% 15.02/2.50  --eq_ax_congr_red                       true
% 15.02/2.50  --pure_diseq_elim                       true
% 15.02/2.50  --brand_transform                       false
% 15.02/2.50  --non_eq_to_eq                          false
% 15.02/2.50  --prep_def_merge                        true
% 15.02/2.50  --prep_def_merge_prop_impl              false
% 15.02/2.50  --prep_def_merge_mbd                    true
% 15.02/2.50  --prep_def_merge_tr_red                 false
% 15.02/2.50  --prep_def_merge_tr_cl                  false
% 15.02/2.50  --smt_preprocessing                     true
% 15.02/2.50  --smt_ac_axioms                         fast
% 15.02/2.50  --preprocessed_out                      false
% 15.02/2.50  --preprocessed_stats                    false
% 15.02/2.50  
% 15.02/2.50  ------ Abstraction refinement Options
% 15.02/2.50  
% 15.02/2.50  --abstr_ref                             []
% 15.02/2.50  --abstr_ref_prep                        false
% 15.02/2.50  --abstr_ref_until_sat                   false
% 15.02/2.50  --abstr_ref_sig_restrict                funpre
% 15.02/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 15.02/2.50  --abstr_ref_under                       []
% 15.02/2.50  
% 15.02/2.50  ------ SAT Options
% 15.02/2.50  
% 15.02/2.50  --sat_mode                              false
% 15.02/2.50  --sat_fm_restart_options                ""
% 15.02/2.50  --sat_gr_def                            false
% 15.02/2.50  --sat_epr_types                         true
% 15.02/2.50  --sat_non_cyclic_types                  false
% 15.02/2.50  --sat_finite_models                     false
% 15.02/2.50  --sat_fm_lemmas                         false
% 15.02/2.50  --sat_fm_prep                           false
% 15.02/2.50  --sat_fm_uc_incr                        true
% 15.02/2.50  --sat_out_model                         small
% 15.02/2.50  --sat_out_clauses                       false
% 15.02/2.50  
% 15.02/2.50  ------ QBF Options
% 15.02/2.50  
% 15.02/2.50  --qbf_mode                              false
% 15.02/2.50  --qbf_elim_univ                         false
% 15.02/2.50  --qbf_dom_inst                          none
% 15.02/2.50  --qbf_dom_pre_inst                      false
% 15.02/2.50  --qbf_sk_in                             false
% 15.02/2.50  --qbf_pred_elim                         true
% 15.02/2.50  --qbf_split                             512
% 15.02/2.50  
% 15.02/2.50  ------ BMC1 Options
% 15.02/2.50  
% 15.02/2.50  --bmc1_incremental                      false
% 15.02/2.50  --bmc1_axioms                           reachable_all
% 15.02/2.50  --bmc1_min_bound                        0
% 15.02/2.50  --bmc1_max_bound                        -1
% 15.02/2.50  --bmc1_max_bound_default                -1
% 15.02/2.50  --bmc1_symbol_reachability              true
% 15.02/2.50  --bmc1_property_lemmas                  false
% 15.02/2.50  --bmc1_k_induction                      false
% 15.02/2.50  --bmc1_non_equiv_states                 false
% 15.02/2.50  --bmc1_deadlock                         false
% 15.02/2.50  --bmc1_ucm                              false
% 15.02/2.50  --bmc1_add_unsat_core                   none
% 15.02/2.50  --bmc1_unsat_core_children              false
% 15.02/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 15.02/2.50  --bmc1_out_stat                         full
% 15.02/2.50  --bmc1_ground_init                      false
% 15.02/2.50  --bmc1_pre_inst_next_state              false
% 15.02/2.50  --bmc1_pre_inst_state                   false
% 15.02/2.50  --bmc1_pre_inst_reach_state             false
% 15.02/2.50  --bmc1_out_unsat_core                   false
% 15.02/2.50  --bmc1_aig_witness_out                  false
% 15.02/2.50  --bmc1_verbose                          false
% 15.02/2.50  --bmc1_dump_clauses_tptp                false
% 15.02/2.50  --bmc1_dump_unsat_core_tptp             false
% 15.02/2.50  --bmc1_dump_file                        -
% 15.02/2.50  --bmc1_ucm_expand_uc_limit              128
% 15.02/2.50  --bmc1_ucm_n_expand_iterations          6
% 15.02/2.50  --bmc1_ucm_extend_mode                  1
% 15.02/2.50  --bmc1_ucm_init_mode                    2
% 15.02/2.50  --bmc1_ucm_cone_mode                    none
% 15.02/2.50  --bmc1_ucm_reduced_relation_type        0
% 15.02/2.50  --bmc1_ucm_relax_model                  4
% 15.02/2.50  --bmc1_ucm_full_tr_after_sat            true
% 15.02/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 15.02/2.50  --bmc1_ucm_layered_model                none
% 15.02/2.50  --bmc1_ucm_max_lemma_size               10
% 15.02/2.50  
% 15.02/2.50  ------ AIG Options
% 15.02/2.50  
% 15.02/2.50  --aig_mode                              false
% 15.02/2.50  
% 15.02/2.50  ------ Instantiation Options
% 15.02/2.50  
% 15.02/2.50  --instantiation_flag                    true
% 15.02/2.50  --inst_sos_flag                         false
% 15.02/2.50  --inst_sos_phase                        true
% 15.02/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.02/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.02/2.50  --inst_lit_sel_side                     none
% 15.02/2.50  --inst_solver_per_active                1400
% 15.02/2.50  --inst_solver_calls_frac                1.
% 15.02/2.50  --inst_passive_queue_type               priority_queues
% 15.02/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.02/2.51  --inst_passive_queues_freq              [25;2]
% 15.02/2.51  --inst_dismatching                      true
% 15.02/2.51  --inst_eager_unprocessed_to_passive     true
% 15.02/2.51  --inst_prop_sim_given                   true
% 15.02/2.51  --inst_prop_sim_new                     false
% 15.02/2.51  --inst_subs_new                         false
% 15.02/2.51  --inst_eq_res_simp                      false
% 15.02/2.51  --inst_subs_given                       false
% 15.02/2.51  --inst_orphan_elimination               true
% 15.02/2.51  --inst_learning_loop_flag               true
% 15.02/2.51  --inst_learning_start                   3000
% 15.02/2.51  --inst_learning_factor                  2
% 15.02/2.51  --inst_start_prop_sim_after_learn       3
% 15.02/2.51  --inst_sel_renew                        solver
% 15.02/2.51  --inst_lit_activity_flag                true
% 15.02/2.51  --inst_restr_to_given                   false
% 15.02/2.51  --inst_activity_threshold               500
% 15.02/2.51  --inst_out_proof                        true
% 15.02/2.51  
% 15.02/2.51  ------ Resolution Options
% 15.02/2.51  
% 15.02/2.51  --resolution_flag                       false
% 15.02/2.51  --res_lit_sel                           adaptive
% 15.02/2.51  --res_lit_sel_side                      none
% 15.02/2.51  --res_ordering                          kbo
% 15.02/2.51  --res_to_prop_solver                    active
% 15.02/2.51  --res_prop_simpl_new                    false
% 15.02/2.51  --res_prop_simpl_given                  true
% 15.02/2.51  --res_passive_queue_type                priority_queues
% 15.02/2.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.02/2.51  --res_passive_queues_freq               [15;5]
% 15.02/2.51  --res_forward_subs                      full
% 15.02/2.51  --res_backward_subs                     full
% 15.02/2.51  --res_forward_subs_resolution           true
% 15.02/2.51  --res_backward_subs_resolution          true
% 15.02/2.51  --res_orphan_elimination                true
% 15.02/2.51  --res_time_limit                        2.
% 15.02/2.51  --res_out_proof                         true
% 15.02/2.51  
% 15.02/2.51  ------ Superposition Options
% 15.02/2.51  
% 15.02/2.51  --superposition_flag                    true
% 15.02/2.51  --sup_passive_queue_type                priority_queues
% 15.02/2.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.02/2.51  --sup_passive_queues_freq               [8;1;4]
% 15.02/2.51  --demod_completeness_check              fast
% 15.02/2.51  --demod_use_ground                      true
% 15.02/2.51  --sup_to_prop_solver                    passive
% 15.02/2.51  --sup_prop_simpl_new                    true
% 15.02/2.51  --sup_prop_simpl_given                  true
% 15.02/2.51  --sup_fun_splitting                     false
% 15.02/2.51  --sup_smt_interval                      50000
% 15.02/2.51  
% 15.02/2.51  ------ Superposition Simplification Setup
% 15.02/2.51  
% 15.02/2.51  --sup_indices_passive                   []
% 15.02/2.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.02/2.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.02/2.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.02/2.51  --sup_full_triv                         [TrivRules;PropSubs]
% 15.02/2.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.02/2.51  --sup_full_bw                           [BwDemod]
% 15.02/2.51  --sup_immed_triv                        [TrivRules]
% 15.02/2.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.02/2.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.02/2.51  --sup_immed_bw_main                     []
% 15.02/2.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.02/2.51  --sup_input_triv                        [Unflattening;TrivRules]
% 15.02/2.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.02/2.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.02/2.51  
% 15.02/2.51  ------ Combination Options
% 15.02/2.51  
% 15.02/2.51  --comb_res_mult                         3
% 15.02/2.51  --comb_sup_mult                         2
% 15.02/2.51  --comb_inst_mult                        10
% 15.02/2.51  
% 15.02/2.51  ------ Debug Options
% 15.02/2.51  
% 15.02/2.51  --dbg_backtrace                         false
% 15.02/2.51  --dbg_dump_prop_clauses                 false
% 15.02/2.51  --dbg_dump_prop_clauses_file            -
% 15.02/2.51  --dbg_out_stat                          false
% 15.02/2.51  
% 15.02/2.51  
% 15.02/2.51  
% 15.02/2.51  
% 15.02/2.51  ------ Proving...
% 15.02/2.51  
% 15.02/2.51  
% 15.02/2.51  % SZS status Theorem for theBenchmark.p
% 15.02/2.51  
% 15.02/2.51  % SZS output start CNFRefutation for theBenchmark.p
% 15.02/2.51  
% 15.02/2.51  fof(f16,axiom,(
% 15.02/2.51    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) <=> ~r2_hidden(X0,X1))),
% 15.02/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.02/2.51  
% 15.02/2.51  fof(f20,plain,(
% 15.02/2.51    ! [X0,X1] : (~r2_hidden(X0,X1) => k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0))),
% 15.02/2.51    inference(unused_predicate_definition_removal,[],[f16])).
% 15.02/2.51  
% 15.02/2.51  fof(f24,plain,(
% 15.02/2.51    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r2_hidden(X0,X1))),
% 15.02/2.51    inference(ennf_transformation,[],[f20])).
% 15.02/2.51  
% 15.02/2.51  fof(f43,plain,(
% 15.02/2.51    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r2_hidden(X0,X1)) )),
% 15.02/2.51    inference(cnf_transformation,[],[f24])).
% 15.02/2.51  
% 15.02/2.51  fof(f6,axiom,(
% 15.02/2.51    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 15.02/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.02/2.51  
% 15.02/2.51  fof(f33,plain,(
% 15.02/2.51    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 15.02/2.51    inference(cnf_transformation,[],[f6])).
% 15.02/2.51  
% 15.02/2.51  fof(f8,axiom,(
% 15.02/2.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 15.02/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.02/2.51  
% 15.02/2.51  fof(f35,plain,(
% 15.02/2.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 15.02/2.51    inference(cnf_transformation,[],[f8])).
% 15.02/2.51  
% 15.02/2.51  fof(f9,axiom,(
% 15.02/2.51    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 15.02/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.02/2.51  
% 15.02/2.51  fof(f36,plain,(
% 15.02/2.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 15.02/2.51    inference(cnf_transformation,[],[f9])).
% 15.02/2.51  
% 15.02/2.51  fof(f10,axiom,(
% 15.02/2.51    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 15.02/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.02/2.51  
% 15.02/2.51  fof(f37,plain,(
% 15.02/2.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 15.02/2.51    inference(cnf_transformation,[],[f10])).
% 15.02/2.51  
% 15.02/2.51  fof(f11,axiom,(
% 15.02/2.51    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 15.02/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.02/2.51  
% 15.02/2.51  fof(f38,plain,(
% 15.02/2.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 15.02/2.51    inference(cnf_transformation,[],[f11])).
% 15.02/2.51  
% 15.02/2.51  fof(f12,axiom,(
% 15.02/2.51    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 15.02/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.02/2.51  
% 15.02/2.51  fof(f39,plain,(
% 15.02/2.51    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 15.02/2.51    inference(cnf_transformation,[],[f12])).
% 15.02/2.51  
% 15.02/2.51  fof(f13,axiom,(
% 15.02/2.51    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 15.02/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.02/2.51  
% 15.02/2.51  fof(f40,plain,(
% 15.02/2.51    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 15.02/2.51    inference(cnf_transformation,[],[f13])).
% 15.02/2.51  
% 15.02/2.51  fof(f14,axiom,(
% 15.02/2.51    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 15.02/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.02/2.51  
% 15.02/2.51  fof(f41,plain,(
% 15.02/2.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 15.02/2.51    inference(cnf_transformation,[],[f14])).
% 15.02/2.51  
% 15.02/2.51  fof(f46,plain,(
% 15.02/2.51    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 15.02/2.51    inference(definition_unfolding,[],[f40,f41])).
% 15.02/2.51  
% 15.02/2.51  fof(f47,plain,(
% 15.02/2.51    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 15.02/2.51    inference(definition_unfolding,[],[f39,f46])).
% 15.02/2.51  
% 15.02/2.51  fof(f48,plain,(
% 15.02/2.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 15.02/2.51    inference(definition_unfolding,[],[f38,f47])).
% 15.02/2.51  
% 15.02/2.51  fof(f49,plain,(
% 15.02/2.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 15.02/2.51    inference(definition_unfolding,[],[f37,f48])).
% 15.02/2.51  
% 15.02/2.51  fof(f50,plain,(
% 15.02/2.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 15.02/2.51    inference(definition_unfolding,[],[f36,f49])).
% 15.02/2.51  
% 15.02/2.51  fof(f51,plain,(
% 15.02/2.51    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 15.02/2.51    inference(definition_unfolding,[],[f35,f50])).
% 15.02/2.51  
% 15.02/2.51  fof(f53,plain,(
% 15.02/2.51    ( ! [X0,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | r2_hidden(X0,X1)) )),
% 15.02/2.51    inference(definition_unfolding,[],[f43,f33,f51,f51])).
% 15.02/2.51  
% 15.02/2.51  fof(f15,axiom,(
% 15.02/2.51    ! [X0,X1] : (r2_hidden(X0,X1) => k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0))),
% 15.02/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.02/2.51  
% 15.02/2.51  fof(f23,plain,(
% 15.02/2.51    ! [X0,X1] : (k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) | ~r2_hidden(X0,X1))),
% 15.02/2.51    inference(ennf_transformation,[],[f15])).
% 15.02/2.51  
% 15.02/2.51  fof(f42,plain,(
% 15.02/2.51    ( ! [X0,X1] : (k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) | ~r2_hidden(X0,X1)) )),
% 15.02/2.51    inference(cnf_transformation,[],[f23])).
% 15.02/2.51  
% 15.02/2.51  fof(f52,plain,(
% 15.02/2.51    ( ! [X0,X1] : (k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | ~r2_hidden(X0,X1)) )),
% 15.02/2.51    inference(definition_unfolding,[],[f42,f51,f51])).
% 15.02/2.51  
% 15.02/2.51  fof(f4,axiom,(
% 15.02/2.51    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 15.02/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.02/2.51  
% 15.02/2.51  fof(f19,plain,(
% 15.02/2.51    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 15.02/2.51    inference(rectify,[],[f4])).
% 15.02/2.51  
% 15.02/2.51  fof(f31,plain,(
% 15.02/2.51    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 15.02/2.51    inference(cnf_transformation,[],[f19])).
% 15.02/2.51  
% 15.02/2.51  fof(f7,axiom,(
% 15.02/2.51    ! [X0,X1,X2] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))),
% 15.02/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.02/2.51  
% 15.02/2.51  fof(f34,plain,(
% 15.02/2.51    ( ! [X2,X0,X1] : (k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))) )),
% 15.02/2.51    inference(cnf_transformation,[],[f7])).
% 15.02/2.51  
% 15.02/2.51  fof(f2,axiom,(
% 15.02/2.51    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 15.02/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.02/2.51  
% 15.02/2.51  fof(f29,plain,(
% 15.02/2.51    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 15.02/2.51    inference(cnf_transformation,[],[f2])).
% 15.02/2.51  
% 15.02/2.51  fof(f1,axiom,(
% 15.02/2.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 15.02/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.02/2.51  
% 15.02/2.51  fof(f28,plain,(
% 15.02/2.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 15.02/2.51    inference(cnf_transformation,[],[f1])).
% 15.02/2.51  
% 15.02/2.51  fof(f17,conjecture,(
% 15.02/2.51    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 15.02/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.02/2.51  
% 15.02/2.51  fof(f18,negated_conjecture,(
% 15.02/2.51    ~! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 15.02/2.51    inference(negated_conjecture,[],[f17])).
% 15.02/2.51  
% 15.02/2.51  fof(f25,plain,(
% 15.02/2.51    ? [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1))),
% 15.02/2.51    inference(ennf_transformation,[],[f18])).
% 15.02/2.51  
% 15.02/2.51  fof(f26,plain,(
% 15.02/2.51    ? [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) => (k4_xboole_0(k1_tarski(sK0),sK1) != k1_tarski(sK0) & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1))),
% 15.02/2.51    introduced(choice_axiom,[])).
% 15.02/2.51  
% 15.02/2.51  fof(f27,plain,(
% 15.02/2.51    k4_xboole_0(k1_tarski(sK0),sK1) != k1_tarski(sK0) & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 15.02/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f26])).
% 15.02/2.51  
% 15.02/2.51  fof(f45,plain,(
% 15.02/2.51    k4_xboole_0(k1_tarski(sK0),sK1) != k1_tarski(sK0)),
% 15.02/2.51    inference(cnf_transformation,[],[f27])).
% 15.02/2.51  
% 15.02/2.51  fof(f54,plain,(
% 15.02/2.51    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 15.02/2.51    inference(definition_unfolding,[],[f45,f33,f51,f51])).
% 15.02/2.51  
% 15.02/2.51  fof(f3,axiom,(
% 15.02/2.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 15.02/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.02/2.51  
% 15.02/2.51  fof(f21,plain,(
% 15.02/2.51    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 15.02/2.51    inference(unused_predicate_definition_removal,[],[f3])).
% 15.02/2.51  
% 15.02/2.51  fof(f22,plain,(
% 15.02/2.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 15.02/2.51    inference(ennf_transformation,[],[f21])).
% 15.02/2.51  
% 15.02/2.51  fof(f30,plain,(
% 15.02/2.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 15.02/2.51    inference(cnf_transformation,[],[f22])).
% 15.02/2.51  
% 15.02/2.51  fof(f5,axiom,(
% 15.02/2.51    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 15.02/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.02/2.51  
% 15.02/2.51  fof(f32,plain,(
% 15.02/2.51    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 15.02/2.51    inference(cnf_transformation,[],[f5])).
% 15.02/2.51  
% 15.02/2.51  fof(f44,plain,(
% 15.02/2.51    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 15.02/2.51    inference(cnf_transformation,[],[f27])).
% 15.02/2.51  
% 15.02/2.51  fof(f55,plain,(
% 15.02/2.51    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_xboole_0),
% 15.02/2.51    inference(definition_unfolding,[],[f44,f33,f51])).
% 15.02/2.51  
% 15.02/2.51  cnf(c_7,plain,
% 15.02/2.51      ( r2_hidden(X0,X1)
% 15.02/2.51      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 15.02/2.51      inference(cnf_transformation,[],[f53]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(c_151,plain,
% 15.02/2.51      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 15.02/2.51      | r2_hidden(X0,X1) = iProver_top ),
% 15.02/2.51      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(c_6,plain,
% 15.02/2.51      ( ~ r2_hidden(X0,X1)
% 15.02/2.51      | k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 15.02/2.51      inference(cnf_transformation,[],[f52]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(c_152,plain,
% 15.02/2.51      ( k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
% 15.02/2.51      | r2_hidden(X1,X0) != iProver_top ),
% 15.02/2.51      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(c_924,plain,
% 15.02/2.51      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 15.02/2.51      | k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 15.02/2.51      inference(superposition,[status(thm)],[c_151,c_152]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(c_3,plain,
% 15.02/2.51      ( k3_xboole_0(X0,X0) = X0 ),
% 15.02/2.51      inference(cnf_transformation,[],[f31]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(c_5,plain,
% 15.02/2.51      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
% 15.02/2.51      inference(cnf_transformation,[],[f34]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(c_372,plain,
% 15.02/2.51      ( k5_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(k5_xboole_0(X0,X1),X1) ),
% 15.02/2.51      inference(superposition,[status(thm)],[c_3,c_5]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(c_1,plain,
% 15.02/2.51      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 15.02/2.51      inference(cnf_transformation,[],[f29]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(c_1050,plain,
% 15.02/2.51      ( k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X1,X0),X0) ),
% 15.02/2.51      inference(superposition,[status(thm)],[c_372,c_1]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(c_368,plain,
% 15.02/2.51      ( k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0) ),
% 15.02/2.51      inference(superposition,[status(thm)],[c_3,c_5]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(c_1699,plain,
% 15.02/2.51      ( k3_xboole_0(k5_xboole_0(X0,X1),X0) = k3_xboole_0(k5_xboole_0(X1,X0),X0) ),
% 15.02/2.51      inference(superposition,[status(thm)],[c_1050,c_368]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(c_0,plain,
% 15.02/2.51      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 15.02/2.51      inference(cnf_transformation,[],[f28]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(c_3973,plain,
% 15.02/2.51      ( k3_xboole_0(X0,k5_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0) ),
% 15.02/2.51      inference(superposition,[status(thm)],[c_1699,c_0]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(c_572,plain,
% 15.02/2.51      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(k5_xboole_0(X0,X1),X0) ),
% 15.02/2.51      inference(superposition,[status(thm)],[c_0,c_368]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(c_5092,plain,
% 15.02/2.51      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X1,X0)) ),
% 15.02/2.51      inference(demodulation,[status(thm)],[c_3973,c_572]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(c_44456,plain,
% 15.02/2.51      ( k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
% 15.02/2.51      | k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
% 15.02/2.51      inference(demodulation,[status(thm)],[c_924,c_5092]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(c_8,negated_conjecture,
% 15.02/2.51      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 15.02/2.51      inference(cnf_transformation,[],[f54]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(c_199,plain,
% 15.02/2.51      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 15.02/2.51      inference(demodulation,[status(thm)],[c_0,c_8]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(c_566,plain,
% 15.02/2.51      ( k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 15.02/2.51      inference(demodulation,[status(thm)],[c_368,c_199]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(c_686,plain,
% 15.02/2.51      ( k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 15.02/2.51      inference(superposition,[status(thm)],[c_0,c_566]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(c_748,plain,
% 15.02/2.51      ( k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 15.02/2.51      inference(superposition,[status(thm)],[c_1,c_686]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(c_44525,plain,
% 15.02/2.51      ( k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 15.02/2.51      inference(superposition,[status(thm)],[c_44456,c_748]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(c_1689,plain,
% 15.02/2.51      ( k3_xboole_0(k5_xboole_0(X0,X1),X1) = k3_xboole_0(k5_xboole_0(X1,X0),X1) ),
% 15.02/2.51      inference(superposition,[status(thm)],[c_368,c_1050]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(c_3776,plain,
% 15.02/2.51      ( k3_xboole_0(X0,k5_xboole_0(X0,X1)) = k3_xboole_0(k5_xboole_0(X1,X0),X0) ),
% 15.02/2.51      inference(superposition,[status(thm)],[c_1689,c_0]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(c_4937,plain,
% 15.02/2.51      ( k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1)) ),
% 15.02/2.51      inference(demodulation,[status(thm)],[c_3776,c_1050]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(c_45369,plain,
% 15.02/2.51      ( k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
% 15.02/2.51      inference(superposition,[status(thm)],[c_44525,c_4937]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(c_574,plain,
% 15.02/2.51      ( k3_xboole_0(k5_xboole_0(X0,X0),X0) = k5_xboole_0(X0,X0) ),
% 15.02/2.51      inference(superposition,[status(thm)],[c_3,c_368]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(c_1021,plain,
% 15.02/2.51      ( k3_xboole_0(X0,k5_xboole_0(X0,X0)) = k5_xboole_0(X0,X0) ),
% 15.02/2.51      inference(superposition,[status(thm)],[c_574,c_0]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(c_2,plain,
% 15.02/2.51      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 15.02/2.51      inference(cnf_transformation,[],[f30]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(c_4,plain,
% 15.02/2.51      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
% 15.02/2.51      inference(cnf_transformation,[],[f32]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(c_64,plain,
% 15.02/2.51      ( k5_xboole_0(X0,X1) != X2
% 15.02/2.51      | k3_xboole_0(X0,X1) != X3
% 15.02/2.51      | k3_xboole_0(X3,X2) = k1_xboole_0 ),
% 15.02/2.51      inference(resolution_lifted,[status(thm)],[c_2,c_4]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(c_65,plain,
% 15.02/2.51      ( k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = k1_xboole_0 ),
% 15.02/2.51      inference(unflattening,[status(thm)],[c_64]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(c_306,plain,
% 15.02/2.51      ( k3_xboole_0(X0,k5_xboole_0(X0,X0)) = k1_xboole_0 ),
% 15.02/2.51      inference(superposition,[status(thm)],[c_3,c_65]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(c_1026,plain,
% 15.02/2.51      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 15.02/2.51      inference(light_normalisation,[status(thm)],[c_1021,c_306]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(c_45404,plain,
% 15.02/2.51      ( k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = k1_xboole_0 ),
% 15.02/2.51      inference(demodulation,[status(thm)],[c_45369,c_1026]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(c_9,negated_conjecture,
% 15.02/2.51      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_xboole_0 ),
% 15.02/2.51      inference(cnf_transformation,[],[f55]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(c_200,plain,
% 15.02/2.51      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) != k1_xboole_0 ),
% 15.02/2.51      inference(demodulation,[status(thm)],[c_0,c_9]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(c_567,plain,
% 15.02/2.51      ( k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k1_xboole_0 ),
% 15.02/2.51      inference(demodulation,[status(thm)],[c_368,c_200]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(c_600,plain,
% 15.02/2.51      ( k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_xboole_0 ),
% 15.02/2.51      inference(superposition,[status(thm)],[c_0,c_567]) ).
% 15.02/2.51  
% 15.02/2.51  cnf(contradiction,plain,
% 15.02/2.51      ( $false ),
% 15.02/2.51      inference(minisat,[status(thm)],[c_45404,c_600]) ).
% 15.02/2.51  
% 15.02/2.51  
% 15.02/2.51  % SZS output end CNFRefutation for theBenchmark.p
% 15.02/2.51  
% 15.02/2.51  ------                               Statistics
% 15.02/2.51  
% 15.02/2.51  ------ General
% 15.02/2.51  
% 15.02/2.51  abstr_ref_over_cycles:                  0
% 15.02/2.51  abstr_ref_under_cycles:                 0
% 15.02/2.51  gc_basic_clause_elim:                   0
% 15.02/2.51  forced_gc_time:                         0
% 15.02/2.51  parsing_time:                           0.009
% 15.02/2.51  unif_index_cands_time:                  0.
% 15.02/2.51  unif_index_add_time:                    0.
% 15.02/2.51  orderings_time:                         0.
% 15.02/2.51  out_proof_time:                         0.011
% 15.02/2.51  total_time:                             1.565
% 15.02/2.51  num_of_symbols:                         39
% 15.02/2.51  num_of_terms:                           48838
% 15.02/2.51  
% 15.02/2.51  ------ Preprocessing
% 15.02/2.51  
% 15.02/2.51  num_of_splits:                          0
% 15.02/2.51  num_of_split_atoms:                     0
% 15.02/2.51  num_of_reused_defs:                     0
% 15.02/2.51  num_eq_ax_congr_red:                    6
% 15.02/2.51  num_of_sem_filtered_clauses:            1
% 15.02/2.51  num_of_subtypes:                        0
% 15.02/2.51  monotx_restored_types:                  0
% 15.02/2.51  sat_num_of_epr_types:                   0
% 15.02/2.51  sat_num_of_non_cyclic_types:            0
% 15.02/2.51  sat_guarded_non_collapsed_types:        0
% 15.02/2.51  num_pure_diseq_elim:                    0
% 15.02/2.51  simp_replaced_by:                       0
% 15.02/2.51  res_preprocessed:                       48
% 15.02/2.51  prep_upred:                             0
% 15.02/2.51  prep_unflattend:                        2
% 15.02/2.51  smt_new_axioms:                         0
% 15.02/2.51  pred_elim_cands:                        1
% 15.02/2.51  pred_elim:                              1
% 15.02/2.51  pred_elim_cl:                           1
% 15.02/2.51  pred_elim_cycles:                       3
% 15.02/2.51  merged_defs:                            0
% 15.02/2.51  merged_defs_ncl:                        0
% 15.02/2.51  bin_hyper_res:                          0
% 15.02/2.51  prep_cycles:                            4
% 15.02/2.51  pred_elim_time:                         0.
% 15.02/2.51  splitting_time:                         0.
% 15.02/2.51  sem_filter_time:                        0.
% 15.02/2.51  monotx_time:                            0.001
% 15.02/2.51  subtype_inf_time:                       0.
% 15.02/2.51  
% 15.02/2.51  ------ Problem properties
% 15.02/2.51  
% 15.02/2.51  clauses:                                9
% 15.02/2.51  conjectures:                            2
% 15.02/2.51  epr:                                    0
% 15.02/2.51  horn:                                   8
% 15.02/2.51  ground:                                 2
% 15.02/2.51  unary:                                  7
% 15.02/2.51  binary:                                 2
% 15.02/2.51  lits:                                   11
% 15.02/2.51  lits_eq:                                9
% 15.02/2.51  fd_pure:                                0
% 15.02/2.51  fd_pseudo:                              0
% 15.02/2.51  fd_cond:                                0
% 15.02/2.51  fd_pseudo_cond:                         0
% 15.02/2.51  ac_symbols:                             0
% 15.02/2.51  
% 15.02/2.51  ------ Propositional Solver
% 15.02/2.51  
% 15.02/2.51  prop_solver_calls:                      34
% 15.02/2.51  prop_fast_solver_calls:                 391
% 15.02/2.51  smt_solver_calls:                       0
% 15.02/2.51  smt_fast_solver_calls:                  0
% 15.02/2.51  prop_num_of_clauses:                    8725
% 15.02/2.51  prop_preprocess_simplified:             10873
% 15.02/2.51  prop_fo_subsumed:                       0
% 15.02/2.51  prop_solver_time:                       0.
% 15.02/2.51  smt_solver_time:                        0.
% 15.02/2.51  smt_fast_solver_time:                   0.
% 15.02/2.51  prop_fast_solver_time:                  0.
% 15.02/2.51  prop_unsat_core_time:                   0.001
% 15.02/2.51  
% 15.02/2.51  ------ QBF
% 15.02/2.51  
% 15.02/2.51  qbf_q_res:                              0
% 15.02/2.51  qbf_num_tautologies:                    0
% 15.02/2.51  qbf_prep_cycles:                        0
% 15.02/2.51  
% 15.02/2.51  ------ BMC1
% 15.02/2.51  
% 15.02/2.51  bmc1_current_bound:                     -1
% 15.02/2.51  bmc1_last_solved_bound:                 -1
% 15.02/2.51  bmc1_unsat_core_size:                   -1
% 15.02/2.51  bmc1_unsat_core_parents_size:           -1
% 15.02/2.51  bmc1_merge_next_fun:                    0
% 15.02/2.51  bmc1_unsat_core_clauses_time:           0.
% 15.02/2.51  
% 15.02/2.51  ------ Instantiation
% 15.02/2.51  
% 15.02/2.51  inst_num_of_clauses:                    2858
% 15.02/2.51  inst_num_in_passive:                    1936
% 15.02/2.51  inst_num_in_active:                     657
% 15.02/2.51  inst_num_in_unprocessed:                265
% 15.02/2.51  inst_num_of_loops:                      850
% 15.02/2.51  inst_num_of_learning_restarts:          0
% 15.02/2.51  inst_num_moves_active_passive:          187
% 15.02/2.51  inst_lit_activity:                      0
% 15.02/2.51  inst_lit_activity_moves:                1
% 15.02/2.51  inst_num_tautologies:                   0
% 15.02/2.51  inst_num_prop_implied:                  0
% 15.02/2.51  inst_num_existing_simplified:           0
% 15.02/2.51  inst_num_eq_res_simplified:             0
% 15.02/2.51  inst_num_child_elim:                    0
% 15.02/2.51  inst_num_of_dismatching_blockings:      1730
% 15.02/2.51  inst_num_of_non_proper_insts:           2649
% 15.02/2.51  inst_num_of_duplicates:                 0
% 15.02/2.51  inst_inst_num_from_inst_to_res:         0
% 15.02/2.51  inst_dismatching_checking_time:         0.
% 15.02/2.51  
% 15.02/2.51  ------ Resolution
% 15.02/2.51  
% 15.02/2.51  res_num_of_clauses:                     0
% 15.02/2.51  res_num_in_passive:                     0
% 15.02/2.51  res_num_in_active:                      0
% 15.02/2.51  res_num_of_loops:                       52
% 15.02/2.51  res_forward_subset_subsumed:            684
% 15.02/2.51  res_backward_subset_subsumed:           4
% 15.02/2.51  res_forward_subsumed:                   0
% 15.02/2.51  res_backward_subsumed:                  0
% 15.02/2.51  res_forward_subsumption_resolution:     0
% 15.02/2.51  res_backward_subsumption_resolution:    0
% 15.02/2.51  res_clause_to_clause_subsumption:       45722
% 15.02/2.51  res_orphan_elimination:                 0
% 15.02/2.51  res_tautology_del:                      366
% 15.02/2.51  res_num_eq_res_simplified:              0
% 15.02/2.51  res_num_sel_changes:                    0
% 15.02/2.51  res_moves_from_active_to_pass:          0
% 15.02/2.51  
% 15.02/2.51  ------ Superposition
% 15.02/2.51  
% 15.02/2.51  sup_time_total:                         0.
% 15.02/2.51  sup_time_generating:                    0.
% 15.02/2.51  sup_time_sim_full:                      0.
% 15.02/2.51  sup_time_sim_immed:                     0.
% 15.02/2.51  
% 15.02/2.51  sup_num_of_clauses:                     2897
% 15.02/2.51  sup_num_in_active:                      121
% 15.02/2.51  sup_num_in_passive:                     2776
% 15.02/2.51  sup_num_of_loops:                       169
% 15.02/2.51  sup_fw_superposition:                   9291
% 15.02/2.51  sup_bw_superposition:                   6893
% 15.02/2.51  sup_immediate_simplified:               5623
% 15.02/2.51  sup_given_eliminated:                   3
% 15.02/2.51  comparisons_done:                       0
% 15.02/2.51  comparisons_avoided:                    0
% 15.02/2.51  
% 15.02/2.51  ------ Simplifications
% 15.02/2.51  
% 15.02/2.51  
% 15.02/2.51  sim_fw_subset_subsumed:                 0
% 15.02/2.51  sim_bw_subset_subsumed:                 0
% 15.02/2.51  sim_fw_subsumed:                        823
% 15.02/2.51  sim_bw_subsumed:                        92
% 15.02/2.51  sim_fw_subsumption_res:                 0
% 15.02/2.51  sim_bw_subsumption_res:                 0
% 15.02/2.51  sim_tautology_del:                      0
% 15.02/2.51  sim_eq_tautology_del:                   1666
% 15.02/2.51  sim_eq_res_simp:                        0
% 15.02/2.51  sim_fw_demodulated:                     3612
% 15.02/2.51  sim_bw_demodulated:                     118
% 15.02/2.51  sim_light_normalised:                   2383
% 15.02/2.51  sim_joinable_taut:                      0
% 15.02/2.51  sim_joinable_simp:                      0
% 15.02/2.51  sim_ac_normalised:                      0
% 15.02/2.51  sim_smt_subsumption:                    0
% 15.02/2.51  
%------------------------------------------------------------------------------
