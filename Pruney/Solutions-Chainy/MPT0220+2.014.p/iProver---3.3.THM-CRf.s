%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:29:30 EST 2020

% Result     : Theorem 51.52s
% Output     : CNFRefutation 51.52s
% Verified   : 
% Statistics : Number of formulae       :  102 (1897 expanded)
%              Number of clauses        :   46 ( 472 expanded)
%              Number of leaves         :   20 ( 563 expanded)
%              Depth                    :   26
%              Number of atoms          :  108 (1903 expanded)
%              Number of equality atoms :   99 (1894 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f55])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f18])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f45,f51])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f44,f52])).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f43,f53])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f42,f54])).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f48,f56,f55])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f20,conjecture,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1) ),
    inference(negated_conjecture,[],[f20])).

fof(f23,plain,(
    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1) ),
    inference(ennf_transformation,[],[f21])).

fof(f26,plain,
    ( ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1)
   => k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f26])).

fof(f49,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f11,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f40,f33])).

fof(f62,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(definition_unfolding,[],[f49,f50,f56,f55,f55])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f37,f33])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f58,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0))) = X0 ),
    inference(definition_unfolding,[],[f35,f50])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f57,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f34,f50])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f60,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) ),
    inference(definition_unfolding,[],[f38,f33,f33,f50])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_11,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_183,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_184,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2126,plain,
    ( k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(superposition,[status(thm)],[c_183,c_184])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_12,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_320,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_0,c_12])).

cnf(c_176627,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_2126,c_320])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0))) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_727,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8,c_6])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_813,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_727,c_5])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_826,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_813,c_1])).

cnf(c_963,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_826,c_727])).

cnf(c_9,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_10,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_104,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(theory_normalisation,[status(thm)],[c_9,c_10,c_1])).

cnf(c_967,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),X0)))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_826,c_104])).

cnf(c_975,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),X0)))) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_967,c_826])).

cnf(c_976,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(X0,X0)))) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_975,c_8])).

cnf(c_594,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_8,c_10])).

cnf(c_977,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_976,c_594,c_826])).

cnf(c_980,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_963,c_977])).

cnf(c_1110,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_980,c_10])).

cnf(c_1116,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_1110,c_826])).

cnf(c_1545,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X0),X0) = X0 ),
    inference(superposition,[status(thm)],[c_1116,c_6])).

cnf(c_1584,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X0)))) = k3_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1545,c_6])).

cnf(c_1587,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),X0)),k3_xboole_0(X0,X0))))) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X0))) ),
    inference(superposition,[status(thm)],[c_1545,c_104])).

cnf(c_1589,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1545,c_0])).

cnf(c_1591,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),X0)),k3_xboole_0(X0,X0))))) = k5_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_1587,c_1589])).

cnf(c_192,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_10,c_1])).

cnf(c_1417,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(X0,X1)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_980,c_192])).

cnf(c_1420,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_1417,c_813])).

cnf(c_1592,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),X0)),k3_xboole_0(X0,X0))) = k5_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_1591,c_1116,c_1420])).

cnf(c_1593,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X0))) = k5_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_1592,c_1116])).

cnf(c_1594,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(X0,X0)) = k3_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_1584,c_1593])).

cnf(c_1595,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(demodulation,[status(thm)],[c_1594,c_1420])).

cnf(c_1715,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1595,c_980])).

cnf(c_193,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_10,c_1])).

cnf(c_1750,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1715,c_193])).

cnf(c_1752,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_1750,c_813])).

cnf(c_176628,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_176627,c_1752])).

cnf(c_176629,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_176628])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:48:20 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 51.52/7.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 51.52/7.02  
% 51.52/7.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.52/7.02  
% 51.52/7.02  ------  iProver source info
% 51.52/7.02  
% 51.52/7.02  git: date: 2020-06-30 10:37:57 +0100
% 51.52/7.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.52/7.02  git: non_committed_changes: false
% 51.52/7.02  git: last_make_outside_of_git: false
% 51.52/7.02  
% 51.52/7.02  ------ 
% 51.52/7.02  
% 51.52/7.02  ------ Input Options
% 51.52/7.02  
% 51.52/7.02  --out_options                           all
% 51.52/7.02  --tptp_safe_out                         true
% 51.52/7.02  --problem_path                          ""
% 51.52/7.02  --include_path                          ""
% 51.52/7.02  --clausifier                            res/vclausify_rel
% 51.52/7.02  --clausifier_options                    ""
% 51.52/7.02  --stdin                                 false
% 51.52/7.02  --stats_out                             all
% 51.52/7.02  
% 51.52/7.02  ------ General Options
% 51.52/7.02  
% 51.52/7.02  --fof                                   false
% 51.52/7.02  --time_out_real                         305.
% 51.52/7.02  --time_out_virtual                      -1.
% 51.52/7.02  --symbol_type_check                     false
% 51.52/7.02  --clausify_out                          false
% 51.52/7.02  --sig_cnt_out                           false
% 51.52/7.02  --trig_cnt_out                          false
% 51.52/7.02  --trig_cnt_out_tolerance                1.
% 51.52/7.02  --trig_cnt_out_sk_spl                   false
% 51.52/7.02  --abstr_cl_out                          false
% 51.52/7.02  
% 51.52/7.02  ------ Global Options
% 51.52/7.02  
% 51.52/7.02  --schedule                              default
% 51.52/7.02  --add_important_lit                     false
% 51.52/7.02  --prop_solver_per_cl                    1000
% 51.52/7.02  --min_unsat_core                        false
% 51.52/7.02  --soft_assumptions                      false
% 51.52/7.02  --soft_lemma_size                       3
% 51.52/7.02  --prop_impl_unit_size                   0
% 51.52/7.02  --prop_impl_unit                        []
% 51.52/7.02  --share_sel_clauses                     true
% 51.52/7.02  --reset_solvers                         false
% 51.52/7.02  --bc_imp_inh                            [conj_cone]
% 51.52/7.02  --conj_cone_tolerance                   3.
% 51.52/7.02  --extra_neg_conj                        none
% 51.52/7.02  --large_theory_mode                     true
% 51.52/7.02  --prolific_symb_bound                   200
% 51.52/7.02  --lt_threshold                          2000
% 51.52/7.02  --clause_weak_htbl                      true
% 51.52/7.02  --gc_record_bc_elim                     false
% 51.52/7.02  
% 51.52/7.02  ------ Preprocessing Options
% 51.52/7.02  
% 51.52/7.02  --preprocessing_flag                    true
% 51.52/7.02  --time_out_prep_mult                    0.1
% 51.52/7.02  --splitting_mode                        input
% 51.52/7.02  --splitting_grd                         true
% 51.52/7.02  --splitting_cvd                         false
% 51.52/7.02  --splitting_cvd_svl                     false
% 51.52/7.02  --splitting_nvd                         32
% 51.52/7.02  --sub_typing                            true
% 51.52/7.02  --prep_gs_sim                           true
% 51.52/7.02  --prep_unflatten                        true
% 51.52/7.02  --prep_res_sim                          true
% 51.52/7.02  --prep_upred                            true
% 51.52/7.02  --prep_sem_filter                       exhaustive
% 51.52/7.02  --prep_sem_filter_out                   false
% 51.52/7.02  --pred_elim                             true
% 51.52/7.02  --res_sim_input                         true
% 51.52/7.02  --eq_ax_congr_red                       true
% 51.52/7.02  --pure_diseq_elim                       true
% 51.52/7.02  --brand_transform                       false
% 51.52/7.02  --non_eq_to_eq                          false
% 51.52/7.02  --prep_def_merge                        true
% 51.52/7.02  --prep_def_merge_prop_impl              false
% 51.52/7.02  --prep_def_merge_mbd                    true
% 51.52/7.02  --prep_def_merge_tr_red                 false
% 51.52/7.02  --prep_def_merge_tr_cl                  false
% 51.52/7.02  --smt_preprocessing                     true
% 51.52/7.02  --smt_ac_axioms                         fast
% 51.52/7.02  --preprocessed_out                      false
% 51.52/7.02  --preprocessed_stats                    false
% 51.52/7.02  
% 51.52/7.02  ------ Abstraction refinement Options
% 51.52/7.02  
% 51.52/7.02  --abstr_ref                             []
% 51.52/7.02  --abstr_ref_prep                        false
% 51.52/7.02  --abstr_ref_until_sat                   false
% 51.52/7.02  --abstr_ref_sig_restrict                funpre
% 51.52/7.02  --abstr_ref_af_restrict_to_split_sk     false
% 51.52/7.02  --abstr_ref_under                       []
% 51.52/7.02  
% 51.52/7.02  ------ SAT Options
% 51.52/7.02  
% 51.52/7.02  --sat_mode                              false
% 51.52/7.02  --sat_fm_restart_options                ""
% 51.52/7.02  --sat_gr_def                            false
% 51.52/7.02  --sat_epr_types                         true
% 51.52/7.02  --sat_non_cyclic_types                  false
% 51.52/7.02  --sat_finite_models                     false
% 51.52/7.02  --sat_fm_lemmas                         false
% 51.52/7.02  --sat_fm_prep                           false
% 51.52/7.02  --sat_fm_uc_incr                        true
% 51.52/7.02  --sat_out_model                         small
% 51.52/7.02  --sat_out_clauses                       false
% 51.52/7.02  
% 51.52/7.02  ------ QBF Options
% 51.52/7.02  
% 51.52/7.02  --qbf_mode                              false
% 51.52/7.02  --qbf_elim_univ                         false
% 51.52/7.02  --qbf_dom_inst                          none
% 51.52/7.02  --qbf_dom_pre_inst                      false
% 51.52/7.02  --qbf_sk_in                             false
% 51.52/7.02  --qbf_pred_elim                         true
% 51.52/7.02  --qbf_split                             512
% 51.52/7.02  
% 51.52/7.02  ------ BMC1 Options
% 51.52/7.02  
% 51.52/7.02  --bmc1_incremental                      false
% 51.52/7.02  --bmc1_axioms                           reachable_all
% 51.52/7.02  --bmc1_min_bound                        0
% 51.52/7.02  --bmc1_max_bound                        -1
% 51.52/7.02  --bmc1_max_bound_default                -1
% 51.52/7.02  --bmc1_symbol_reachability              true
% 51.52/7.02  --bmc1_property_lemmas                  false
% 51.52/7.02  --bmc1_k_induction                      false
% 51.52/7.02  --bmc1_non_equiv_states                 false
% 51.52/7.02  --bmc1_deadlock                         false
% 51.52/7.02  --bmc1_ucm                              false
% 51.52/7.02  --bmc1_add_unsat_core                   none
% 51.52/7.02  --bmc1_unsat_core_children              false
% 51.52/7.02  --bmc1_unsat_core_extrapolate_axioms    false
% 51.52/7.02  --bmc1_out_stat                         full
% 51.52/7.02  --bmc1_ground_init                      false
% 51.52/7.02  --bmc1_pre_inst_next_state              false
% 51.52/7.02  --bmc1_pre_inst_state                   false
% 51.52/7.02  --bmc1_pre_inst_reach_state             false
% 51.52/7.02  --bmc1_out_unsat_core                   false
% 51.52/7.02  --bmc1_aig_witness_out                  false
% 51.52/7.02  --bmc1_verbose                          false
% 51.52/7.02  --bmc1_dump_clauses_tptp                false
% 51.52/7.02  --bmc1_dump_unsat_core_tptp             false
% 51.52/7.02  --bmc1_dump_file                        -
% 51.52/7.02  --bmc1_ucm_expand_uc_limit              128
% 51.52/7.02  --bmc1_ucm_n_expand_iterations          6
% 51.52/7.02  --bmc1_ucm_extend_mode                  1
% 51.52/7.02  --bmc1_ucm_init_mode                    2
% 51.52/7.02  --bmc1_ucm_cone_mode                    none
% 51.52/7.02  --bmc1_ucm_reduced_relation_type        0
% 51.52/7.02  --bmc1_ucm_relax_model                  4
% 51.52/7.02  --bmc1_ucm_full_tr_after_sat            true
% 51.52/7.02  --bmc1_ucm_expand_neg_assumptions       false
% 51.52/7.02  --bmc1_ucm_layered_model                none
% 51.52/7.02  --bmc1_ucm_max_lemma_size               10
% 51.52/7.02  
% 51.52/7.02  ------ AIG Options
% 51.52/7.02  
% 51.52/7.02  --aig_mode                              false
% 51.52/7.02  
% 51.52/7.02  ------ Instantiation Options
% 51.52/7.02  
% 51.52/7.02  --instantiation_flag                    true
% 51.52/7.02  --inst_sos_flag                         true
% 51.52/7.02  --inst_sos_phase                        true
% 51.52/7.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.52/7.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.52/7.02  --inst_lit_sel_side                     num_symb
% 51.52/7.02  --inst_solver_per_active                1400
% 51.52/7.02  --inst_solver_calls_frac                1.
% 51.52/7.02  --inst_passive_queue_type               priority_queues
% 51.52/7.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.52/7.02  --inst_passive_queues_freq              [25;2]
% 51.52/7.02  --inst_dismatching                      true
% 51.52/7.02  --inst_eager_unprocessed_to_passive     true
% 51.52/7.02  --inst_prop_sim_given                   true
% 51.52/7.02  --inst_prop_sim_new                     false
% 51.52/7.02  --inst_subs_new                         false
% 51.52/7.02  --inst_eq_res_simp                      false
% 51.52/7.02  --inst_subs_given                       false
% 51.52/7.02  --inst_orphan_elimination               true
% 51.52/7.02  --inst_learning_loop_flag               true
% 51.52/7.02  --inst_learning_start                   3000
% 51.52/7.02  --inst_learning_factor                  2
% 51.52/7.02  --inst_start_prop_sim_after_learn       3
% 51.52/7.02  --inst_sel_renew                        solver
% 51.52/7.02  --inst_lit_activity_flag                true
% 51.52/7.02  --inst_restr_to_given                   false
% 51.52/7.02  --inst_activity_threshold               500
% 51.52/7.02  --inst_out_proof                        true
% 51.52/7.02  
% 51.52/7.02  ------ Resolution Options
% 51.52/7.02  
% 51.52/7.02  --resolution_flag                       true
% 51.52/7.02  --res_lit_sel                           adaptive
% 51.52/7.02  --res_lit_sel_side                      none
% 51.52/7.02  --res_ordering                          kbo
% 51.52/7.02  --res_to_prop_solver                    active
% 51.52/7.02  --res_prop_simpl_new                    false
% 51.52/7.02  --res_prop_simpl_given                  true
% 51.52/7.02  --res_passive_queue_type                priority_queues
% 51.52/7.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.52/7.02  --res_passive_queues_freq               [15;5]
% 51.52/7.02  --res_forward_subs                      full
% 51.52/7.02  --res_backward_subs                     full
% 51.52/7.02  --res_forward_subs_resolution           true
% 51.52/7.02  --res_backward_subs_resolution          true
% 51.52/7.02  --res_orphan_elimination                true
% 51.52/7.02  --res_time_limit                        2.
% 51.52/7.02  --res_out_proof                         true
% 51.52/7.02  
% 51.52/7.02  ------ Superposition Options
% 51.52/7.02  
% 51.52/7.02  --superposition_flag                    true
% 51.52/7.02  --sup_passive_queue_type                priority_queues
% 51.52/7.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.52/7.02  --sup_passive_queues_freq               [8;1;4]
% 51.52/7.02  --demod_completeness_check              fast
% 51.52/7.02  --demod_use_ground                      true
% 51.52/7.02  --sup_to_prop_solver                    passive
% 51.52/7.02  --sup_prop_simpl_new                    true
% 51.52/7.02  --sup_prop_simpl_given                  true
% 51.52/7.02  --sup_fun_splitting                     true
% 51.52/7.02  --sup_smt_interval                      50000
% 51.52/7.02  
% 51.52/7.02  ------ Superposition Simplification Setup
% 51.52/7.02  
% 51.52/7.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.52/7.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.52/7.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.52/7.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 51.52/7.02  --sup_full_triv                         [TrivRules;PropSubs]
% 51.52/7.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.52/7.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.52/7.02  --sup_immed_triv                        [TrivRules]
% 51.52/7.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.52/7.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.52/7.02  --sup_immed_bw_main                     []
% 51.52/7.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.52/7.02  --sup_input_triv                        [Unflattening;TrivRules]
% 51.52/7.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.52/7.02  --sup_input_bw                          []
% 51.52/7.02  
% 51.52/7.02  ------ Combination Options
% 51.52/7.02  
% 51.52/7.02  --comb_res_mult                         3
% 51.52/7.02  --comb_sup_mult                         2
% 51.52/7.02  --comb_inst_mult                        10
% 51.52/7.02  
% 51.52/7.02  ------ Debug Options
% 51.52/7.02  
% 51.52/7.02  --dbg_backtrace                         false
% 51.52/7.02  --dbg_dump_prop_clauses                 false
% 51.52/7.02  --dbg_dump_prop_clauses_file            -
% 51.52/7.02  --dbg_out_stat                          false
% 51.52/7.02  ------ Parsing...
% 51.52/7.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.52/7.02  
% 51.52/7.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 51.52/7.02  
% 51.52/7.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.52/7.02  
% 51.52/7.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.52/7.02  ------ Proving...
% 51.52/7.02  ------ Problem Properties 
% 51.52/7.02  
% 51.52/7.02  
% 51.52/7.02  clauses                                 12
% 51.52/7.02  conjectures                             1
% 51.52/7.02  EPR                                     2
% 51.52/7.02  Horn                                    12
% 51.52/7.02  unary                                   10
% 51.52/7.02  binary                                  1
% 51.52/7.02  lits                                    15
% 51.52/7.02  lits eq                                 10
% 51.52/7.02  fd_pure                                 0
% 51.52/7.02  fd_pseudo                               0
% 51.52/7.02  fd_cond                                 0
% 51.52/7.02  fd_pseudo_cond                          1
% 51.52/7.02  AC symbols                              1
% 51.52/7.02  
% 51.52/7.02  ------ Schedule dynamic 5 is on 
% 51.52/7.02  
% 51.52/7.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 51.52/7.02  
% 51.52/7.02  
% 51.52/7.02  ------ 
% 51.52/7.02  Current options:
% 51.52/7.02  ------ 
% 51.52/7.02  
% 51.52/7.02  ------ Input Options
% 51.52/7.02  
% 51.52/7.02  --out_options                           all
% 51.52/7.02  --tptp_safe_out                         true
% 51.52/7.02  --problem_path                          ""
% 51.52/7.02  --include_path                          ""
% 51.52/7.02  --clausifier                            res/vclausify_rel
% 51.52/7.02  --clausifier_options                    ""
% 51.52/7.02  --stdin                                 false
% 51.52/7.02  --stats_out                             all
% 51.52/7.02  
% 51.52/7.02  ------ General Options
% 51.52/7.02  
% 51.52/7.02  --fof                                   false
% 51.52/7.02  --time_out_real                         305.
% 51.52/7.02  --time_out_virtual                      -1.
% 51.52/7.02  --symbol_type_check                     false
% 51.52/7.02  --clausify_out                          false
% 51.52/7.02  --sig_cnt_out                           false
% 51.52/7.02  --trig_cnt_out                          false
% 51.52/7.02  --trig_cnt_out_tolerance                1.
% 51.52/7.02  --trig_cnt_out_sk_spl                   false
% 51.52/7.02  --abstr_cl_out                          false
% 51.52/7.02  
% 51.52/7.02  ------ Global Options
% 51.52/7.02  
% 51.52/7.02  --schedule                              default
% 51.52/7.02  --add_important_lit                     false
% 51.52/7.02  --prop_solver_per_cl                    1000
% 51.52/7.02  --min_unsat_core                        false
% 51.52/7.02  --soft_assumptions                      false
% 51.52/7.02  --soft_lemma_size                       3
% 51.52/7.02  --prop_impl_unit_size                   0
% 51.52/7.02  --prop_impl_unit                        []
% 51.52/7.02  --share_sel_clauses                     true
% 51.52/7.02  --reset_solvers                         false
% 51.52/7.02  --bc_imp_inh                            [conj_cone]
% 51.52/7.02  --conj_cone_tolerance                   3.
% 51.52/7.02  --extra_neg_conj                        none
% 51.52/7.02  --large_theory_mode                     true
% 51.52/7.02  --prolific_symb_bound                   200
% 51.52/7.02  --lt_threshold                          2000
% 51.52/7.02  --clause_weak_htbl                      true
% 51.52/7.02  --gc_record_bc_elim                     false
% 51.52/7.02  
% 51.52/7.02  ------ Preprocessing Options
% 51.52/7.02  
% 51.52/7.02  --preprocessing_flag                    true
% 51.52/7.02  --time_out_prep_mult                    0.1
% 51.52/7.02  --splitting_mode                        input
% 51.52/7.02  --splitting_grd                         true
% 51.52/7.02  --splitting_cvd                         false
% 51.52/7.02  --splitting_cvd_svl                     false
% 51.52/7.02  --splitting_nvd                         32
% 51.52/7.02  --sub_typing                            true
% 51.52/7.02  --prep_gs_sim                           true
% 51.52/7.02  --prep_unflatten                        true
% 51.52/7.02  --prep_res_sim                          true
% 51.52/7.02  --prep_upred                            true
% 51.52/7.02  --prep_sem_filter                       exhaustive
% 51.52/7.02  --prep_sem_filter_out                   false
% 51.52/7.02  --pred_elim                             true
% 51.52/7.02  --res_sim_input                         true
% 51.52/7.02  --eq_ax_congr_red                       true
% 51.52/7.02  --pure_diseq_elim                       true
% 51.52/7.02  --brand_transform                       false
% 51.52/7.02  --non_eq_to_eq                          false
% 51.52/7.02  --prep_def_merge                        true
% 51.52/7.02  --prep_def_merge_prop_impl              false
% 51.52/7.02  --prep_def_merge_mbd                    true
% 51.52/7.02  --prep_def_merge_tr_red                 false
% 51.52/7.02  --prep_def_merge_tr_cl                  false
% 51.52/7.02  --smt_preprocessing                     true
% 51.52/7.02  --smt_ac_axioms                         fast
% 51.52/7.02  --preprocessed_out                      false
% 51.52/7.02  --preprocessed_stats                    false
% 51.52/7.02  
% 51.52/7.02  ------ Abstraction refinement Options
% 51.52/7.02  
% 51.52/7.02  --abstr_ref                             []
% 51.52/7.02  --abstr_ref_prep                        false
% 51.52/7.02  --abstr_ref_until_sat                   false
% 51.52/7.02  --abstr_ref_sig_restrict                funpre
% 51.52/7.02  --abstr_ref_af_restrict_to_split_sk     false
% 51.52/7.02  --abstr_ref_under                       []
% 51.52/7.02  
% 51.52/7.02  ------ SAT Options
% 51.52/7.02  
% 51.52/7.02  --sat_mode                              false
% 51.52/7.02  --sat_fm_restart_options                ""
% 51.52/7.02  --sat_gr_def                            false
% 51.52/7.02  --sat_epr_types                         true
% 51.52/7.02  --sat_non_cyclic_types                  false
% 51.52/7.02  --sat_finite_models                     false
% 51.52/7.02  --sat_fm_lemmas                         false
% 51.52/7.02  --sat_fm_prep                           false
% 51.52/7.02  --sat_fm_uc_incr                        true
% 51.52/7.02  --sat_out_model                         small
% 51.52/7.02  --sat_out_clauses                       false
% 51.52/7.02  
% 51.52/7.02  ------ QBF Options
% 51.52/7.02  
% 51.52/7.02  --qbf_mode                              false
% 51.52/7.02  --qbf_elim_univ                         false
% 51.52/7.02  --qbf_dom_inst                          none
% 51.52/7.02  --qbf_dom_pre_inst                      false
% 51.52/7.02  --qbf_sk_in                             false
% 51.52/7.02  --qbf_pred_elim                         true
% 51.52/7.02  --qbf_split                             512
% 51.52/7.02  
% 51.52/7.02  ------ BMC1 Options
% 51.52/7.02  
% 51.52/7.02  --bmc1_incremental                      false
% 51.52/7.02  --bmc1_axioms                           reachable_all
% 51.52/7.02  --bmc1_min_bound                        0
% 51.52/7.02  --bmc1_max_bound                        -1
% 51.52/7.02  --bmc1_max_bound_default                -1
% 51.52/7.02  --bmc1_symbol_reachability              true
% 51.52/7.02  --bmc1_property_lemmas                  false
% 51.52/7.02  --bmc1_k_induction                      false
% 51.52/7.02  --bmc1_non_equiv_states                 false
% 51.52/7.02  --bmc1_deadlock                         false
% 51.52/7.02  --bmc1_ucm                              false
% 51.52/7.02  --bmc1_add_unsat_core                   none
% 51.52/7.02  --bmc1_unsat_core_children              false
% 51.52/7.02  --bmc1_unsat_core_extrapolate_axioms    false
% 51.52/7.02  --bmc1_out_stat                         full
% 51.52/7.02  --bmc1_ground_init                      false
% 51.52/7.02  --bmc1_pre_inst_next_state              false
% 51.52/7.02  --bmc1_pre_inst_state                   false
% 51.52/7.02  --bmc1_pre_inst_reach_state             false
% 51.52/7.02  --bmc1_out_unsat_core                   false
% 51.52/7.02  --bmc1_aig_witness_out                  false
% 51.52/7.02  --bmc1_verbose                          false
% 51.52/7.02  --bmc1_dump_clauses_tptp                false
% 51.52/7.02  --bmc1_dump_unsat_core_tptp             false
% 51.52/7.02  --bmc1_dump_file                        -
% 51.52/7.02  --bmc1_ucm_expand_uc_limit              128
% 51.52/7.02  --bmc1_ucm_n_expand_iterations          6
% 51.52/7.02  --bmc1_ucm_extend_mode                  1
% 51.52/7.02  --bmc1_ucm_init_mode                    2
% 51.52/7.02  --bmc1_ucm_cone_mode                    none
% 51.52/7.02  --bmc1_ucm_reduced_relation_type        0
% 51.52/7.02  --bmc1_ucm_relax_model                  4
% 51.52/7.02  --bmc1_ucm_full_tr_after_sat            true
% 51.52/7.02  --bmc1_ucm_expand_neg_assumptions       false
% 51.52/7.02  --bmc1_ucm_layered_model                none
% 51.52/7.02  --bmc1_ucm_max_lemma_size               10
% 51.52/7.02  
% 51.52/7.02  ------ AIG Options
% 51.52/7.02  
% 51.52/7.02  --aig_mode                              false
% 51.52/7.02  
% 51.52/7.02  ------ Instantiation Options
% 51.52/7.02  
% 51.52/7.02  --instantiation_flag                    true
% 51.52/7.02  --inst_sos_flag                         true
% 51.52/7.02  --inst_sos_phase                        true
% 51.52/7.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.52/7.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.52/7.02  --inst_lit_sel_side                     none
% 51.52/7.02  --inst_solver_per_active                1400
% 51.52/7.02  --inst_solver_calls_frac                1.
% 51.52/7.02  --inst_passive_queue_type               priority_queues
% 51.52/7.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.52/7.02  --inst_passive_queues_freq              [25;2]
% 51.52/7.02  --inst_dismatching                      true
% 51.52/7.02  --inst_eager_unprocessed_to_passive     true
% 51.52/7.02  --inst_prop_sim_given                   true
% 51.52/7.02  --inst_prop_sim_new                     false
% 51.52/7.02  --inst_subs_new                         false
% 51.52/7.02  --inst_eq_res_simp                      false
% 51.52/7.02  --inst_subs_given                       false
% 51.52/7.02  --inst_orphan_elimination               true
% 51.52/7.02  --inst_learning_loop_flag               true
% 51.52/7.02  --inst_learning_start                   3000
% 51.52/7.02  --inst_learning_factor                  2
% 51.52/7.02  --inst_start_prop_sim_after_learn       3
% 51.52/7.02  --inst_sel_renew                        solver
% 51.52/7.02  --inst_lit_activity_flag                true
% 51.52/7.02  --inst_restr_to_given                   false
% 51.52/7.02  --inst_activity_threshold               500
% 51.52/7.02  --inst_out_proof                        true
% 51.52/7.02  
% 51.52/7.02  ------ Resolution Options
% 51.52/7.02  
% 51.52/7.02  --resolution_flag                       false
% 51.52/7.02  --res_lit_sel                           adaptive
% 51.52/7.02  --res_lit_sel_side                      none
% 51.52/7.02  --res_ordering                          kbo
% 51.52/7.02  --res_to_prop_solver                    active
% 51.52/7.02  --res_prop_simpl_new                    false
% 51.52/7.02  --res_prop_simpl_given                  true
% 51.52/7.02  --res_passive_queue_type                priority_queues
% 51.52/7.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.52/7.02  --res_passive_queues_freq               [15;5]
% 51.52/7.02  --res_forward_subs                      full
% 51.52/7.02  --res_backward_subs                     full
% 51.52/7.02  --res_forward_subs_resolution           true
% 51.52/7.02  --res_backward_subs_resolution          true
% 51.52/7.02  --res_orphan_elimination                true
% 51.52/7.02  --res_time_limit                        2.
% 51.52/7.02  --res_out_proof                         true
% 51.52/7.02  
% 51.52/7.02  ------ Superposition Options
% 51.52/7.02  
% 51.52/7.02  --superposition_flag                    true
% 51.52/7.02  --sup_passive_queue_type                priority_queues
% 51.52/7.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.52/7.02  --sup_passive_queues_freq               [8;1;4]
% 51.52/7.02  --demod_completeness_check              fast
% 51.52/7.02  --demod_use_ground                      true
% 51.52/7.02  --sup_to_prop_solver                    passive
% 51.52/7.02  --sup_prop_simpl_new                    true
% 51.52/7.02  --sup_prop_simpl_given                  true
% 51.52/7.02  --sup_fun_splitting                     true
% 51.52/7.02  --sup_smt_interval                      50000
% 51.52/7.02  
% 51.52/7.02  ------ Superposition Simplification Setup
% 51.52/7.02  
% 51.52/7.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.52/7.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.52/7.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.52/7.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 51.52/7.02  --sup_full_triv                         [TrivRules;PropSubs]
% 51.52/7.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.52/7.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.52/7.02  --sup_immed_triv                        [TrivRules]
% 51.52/7.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.52/7.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.52/7.02  --sup_immed_bw_main                     []
% 51.52/7.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.52/7.02  --sup_input_triv                        [Unflattening;TrivRules]
% 51.52/7.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.52/7.02  --sup_input_bw                          []
% 51.52/7.02  
% 51.52/7.02  ------ Combination Options
% 51.52/7.02  
% 51.52/7.02  --comb_res_mult                         3
% 51.52/7.02  --comb_sup_mult                         2
% 51.52/7.02  --comb_inst_mult                        10
% 51.52/7.02  
% 51.52/7.02  ------ Debug Options
% 51.52/7.02  
% 51.52/7.02  --dbg_backtrace                         false
% 51.52/7.02  --dbg_dump_prop_clauses                 false
% 51.52/7.02  --dbg_dump_prop_clauses_file            -
% 51.52/7.02  --dbg_out_stat                          false
% 51.52/7.02  
% 51.52/7.02  
% 51.52/7.02  
% 51.52/7.02  
% 51.52/7.02  ------ Proving...
% 51.52/7.02  
% 51.52/7.02  
% 51.52/7.02  % SZS status Theorem for theBenchmark.p
% 51.52/7.02  
% 51.52/7.02   Resolution empty clause
% 51.52/7.02  
% 51.52/7.02  % SZS output start CNFRefutation for theBenchmark.p
% 51.52/7.02  
% 51.52/7.02  fof(f19,axiom,(
% 51.52/7.02    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 51.52/7.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.52/7.02  
% 51.52/7.02  fof(f48,plain,(
% 51.52/7.02    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 51.52/7.02    inference(cnf_transformation,[],[f19])).
% 51.52/7.02  
% 51.52/7.02  fof(f12,axiom,(
% 51.52/7.02    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 51.52/7.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.52/7.02  
% 51.52/7.02  fof(f41,plain,(
% 51.52/7.02    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 51.52/7.02    inference(cnf_transformation,[],[f12])).
% 51.52/7.02  
% 51.52/7.02  fof(f56,plain,(
% 51.52/7.02    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 51.52/7.02    inference(definition_unfolding,[],[f41,f55])).
% 51.52/7.02  
% 51.52/7.02  fof(f13,axiom,(
% 51.52/7.02    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 51.52/7.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.52/7.02  
% 51.52/7.02  fof(f42,plain,(
% 51.52/7.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 51.52/7.02    inference(cnf_transformation,[],[f13])).
% 51.52/7.02  
% 51.52/7.02  fof(f14,axiom,(
% 51.52/7.02    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 51.52/7.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.52/7.02  
% 51.52/7.02  fof(f43,plain,(
% 51.52/7.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 51.52/7.02    inference(cnf_transformation,[],[f14])).
% 51.52/7.02  
% 51.52/7.02  fof(f15,axiom,(
% 51.52/7.02    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 51.52/7.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.52/7.02  
% 51.52/7.02  fof(f44,plain,(
% 51.52/7.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 51.52/7.02    inference(cnf_transformation,[],[f15])).
% 51.52/7.02  
% 51.52/7.02  fof(f16,axiom,(
% 51.52/7.02    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 51.52/7.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.52/7.02  
% 51.52/7.02  fof(f45,plain,(
% 51.52/7.02    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 51.52/7.02    inference(cnf_transformation,[],[f16])).
% 51.52/7.02  
% 51.52/7.02  fof(f17,axiom,(
% 51.52/7.02    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 51.52/7.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.52/7.02  
% 51.52/7.02  fof(f46,plain,(
% 51.52/7.02    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 51.52/7.02    inference(cnf_transformation,[],[f17])).
% 51.52/7.02  
% 51.52/7.02  fof(f18,axiom,(
% 51.52/7.02    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 51.52/7.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.52/7.02  
% 51.52/7.02  fof(f47,plain,(
% 51.52/7.02    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 51.52/7.02    inference(cnf_transformation,[],[f18])).
% 51.52/7.02  
% 51.52/7.02  fof(f51,plain,(
% 51.52/7.02    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 51.52/7.02    inference(definition_unfolding,[],[f46,f47])).
% 51.52/7.02  
% 51.52/7.02  fof(f52,plain,(
% 51.52/7.02    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 51.52/7.02    inference(definition_unfolding,[],[f45,f51])).
% 51.52/7.02  
% 51.52/7.02  fof(f53,plain,(
% 51.52/7.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 51.52/7.02    inference(definition_unfolding,[],[f44,f52])).
% 51.52/7.02  
% 51.52/7.02  fof(f54,plain,(
% 51.52/7.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 51.52/7.02    inference(definition_unfolding,[],[f43,f53])).
% 51.52/7.02  
% 51.52/7.02  fof(f55,plain,(
% 51.52/7.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 51.52/7.02    inference(definition_unfolding,[],[f42,f54])).
% 51.52/7.02  
% 51.52/7.02  fof(f61,plain,(
% 51.52/7.02    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 51.52/7.02    inference(definition_unfolding,[],[f48,f56,f55])).
% 51.52/7.02  
% 51.52/7.02  fof(f7,axiom,(
% 51.52/7.02    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 51.52/7.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.52/7.02  
% 51.52/7.02  fof(f22,plain,(
% 51.52/7.02    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 51.52/7.02    inference(ennf_transformation,[],[f7])).
% 51.52/7.02  
% 51.52/7.02  fof(f36,plain,(
% 51.52/7.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 51.52/7.02    inference(cnf_transformation,[],[f22])).
% 51.52/7.02  
% 51.52/7.02  fof(f1,axiom,(
% 51.52/7.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 51.52/7.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.52/7.02  
% 51.52/7.02  fof(f28,plain,(
% 51.52/7.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 51.52/7.02    inference(cnf_transformation,[],[f1])).
% 51.52/7.02  
% 51.52/7.02  fof(f20,conjecture,(
% 51.52/7.02    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1)),
% 51.52/7.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.52/7.02  
% 51.52/7.02  fof(f21,negated_conjecture,(
% 51.52/7.02    ~! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1)),
% 51.52/7.02    inference(negated_conjecture,[],[f20])).
% 51.52/7.02  
% 51.52/7.02  fof(f23,plain,(
% 51.52/7.02    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1)),
% 51.52/7.02    inference(ennf_transformation,[],[f21])).
% 51.52/7.02  
% 51.52/7.02  fof(f26,plain,(
% 51.52/7.02    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) != k2_tarski(X0,X1) => k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1)),
% 51.52/7.02    introduced(choice_axiom,[])).
% 51.52/7.02  
% 51.52/7.02  fof(f27,plain,(
% 51.52/7.02    k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1)),
% 51.52/7.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f26])).
% 51.52/7.02  
% 51.52/7.02  fof(f49,plain,(
% 51.52/7.02    k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) != k2_tarski(sK0,sK1)),
% 51.52/7.02    inference(cnf_transformation,[],[f27])).
% 51.52/7.02  
% 51.52/7.02  fof(f11,axiom,(
% 51.52/7.02    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 51.52/7.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.52/7.02  
% 51.52/7.02  fof(f40,plain,(
% 51.52/7.02    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 51.52/7.02    inference(cnf_transformation,[],[f11])).
% 51.52/7.02  
% 51.52/7.02  fof(f4,axiom,(
% 51.52/7.02    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 51.52/7.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.52/7.02  
% 51.52/7.02  fof(f33,plain,(
% 51.52/7.02    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 51.52/7.02    inference(cnf_transformation,[],[f4])).
% 51.52/7.02  
% 51.52/7.02  fof(f50,plain,(
% 51.52/7.02    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 51.52/7.02    inference(definition_unfolding,[],[f40,f33])).
% 51.52/7.02  
% 51.52/7.02  fof(f62,plain,(
% 51.52/7.02    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 51.52/7.02    inference(definition_unfolding,[],[f49,f50,f56,f55,f55])).
% 51.52/7.02  
% 51.52/7.02  fof(f8,axiom,(
% 51.52/7.02    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 51.52/7.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.52/7.02  
% 51.52/7.02  fof(f37,plain,(
% 51.52/7.02    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 51.52/7.02    inference(cnf_transformation,[],[f8])).
% 51.52/7.02  
% 51.52/7.02  fof(f59,plain,(
% 51.52/7.02    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 51.52/7.02    inference(definition_unfolding,[],[f37,f33])).
% 51.52/7.02  
% 51.52/7.02  fof(f6,axiom,(
% 51.52/7.02    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 51.52/7.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.52/7.02  
% 51.52/7.02  fof(f35,plain,(
% 51.52/7.02    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 51.52/7.02    inference(cnf_transformation,[],[f6])).
% 51.52/7.02  
% 51.52/7.02  fof(f58,plain,(
% 51.52/7.02    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0))) = X0) )),
% 51.52/7.02    inference(definition_unfolding,[],[f35,f50])).
% 51.52/7.02  
% 51.52/7.02  fof(f5,axiom,(
% 51.52/7.02    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 51.52/7.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.52/7.02  
% 51.52/7.02  fof(f34,plain,(
% 51.52/7.02    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 51.52/7.02    inference(cnf_transformation,[],[f5])).
% 51.52/7.02  
% 51.52/7.02  fof(f57,plain,(
% 51.52/7.02    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 51.52/7.02    inference(definition_unfolding,[],[f34,f50])).
% 51.52/7.02  
% 51.52/7.02  fof(f2,axiom,(
% 51.52/7.02    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 51.52/7.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.52/7.02  
% 51.52/7.02  fof(f29,plain,(
% 51.52/7.02    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 51.52/7.02    inference(cnf_transformation,[],[f2])).
% 51.52/7.02  
% 51.52/7.02  fof(f9,axiom,(
% 51.52/7.02    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 51.52/7.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.52/7.02  
% 51.52/7.02  fof(f38,plain,(
% 51.52/7.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 51.52/7.02    inference(cnf_transformation,[],[f9])).
% 51.52/7.02  
% 51.52/7.02  fof(f60,plain,(
% 51.52/7.02    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1))) )),
% 51.52/7.02    inference(definition_unfolding,[],[f38,f33,f33,f50])).
% 51.52/7.02  
% 51.52/7.02  fof(f10,axiom,(
% 51.52/7.02    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 51.52/7.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.52/7.02  
% 51.52/7.02  fof(f39,plain,(
% 51.52/7.02    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 51.52/7.02    inference(cnf_transformation,[],[f10])).
% 51.52/7.02  
% 51.52/7.02  cnf(c_11,plain,
% 51.52/7.02      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 51.52/7.02      inference(cnf_transformation,[],[f61]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_183,plain,
% 51.52/7.02      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
% 51.52/7.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_7,plain,
% 51.52/7.02      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 51.52/7.02      inference(cnf_transformation,[],[f36]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_184,plain,
% 51.52/7.02      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 51.52/7.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_2126,plain,
% 51.52/7.02      ( k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 51.52/7.02      inference(superposition,[status(thm)],[c_183,c_184]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_0,plain,
% 51.52/7.02      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 51.52/7.02      inference(cnf_transformation,[],[f28]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_12,negated_conjecture,
% 51.52/7.02      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 51.52/7.02      inference(cnf_transformation,[],[f62]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_320,plain,
% 51.52/7.02      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 51.52/7.02      inference(demodulation,[status(thm)],[c_0,c_12]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_176627,plain,
% 51.52/7.02      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 51.52/7.02      inference(demodulation,[status(thm)],[c_2126,c_320]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_8,plain,
% 51.52/7.02      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 51.52/7.02      inference(cnf_transformation,[],[f59]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_6,plain,
% 51.52/7.02      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0))) = X0 ),
% 51.52/7.02      inference(cnf_transformation,[],[f58]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_727,plain,
% 51.52/7.02      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 51.52/7.02      inference(superposition,[status(thm)],[c_8,c_6]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_5,plain,
% 51.52/7.02      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
% 51.52/7.02      inference(cnf_transformation,[],[f57]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_813,plain,
% 51.52/7.02      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 51.52/7.02      inference(demodulation,[status(thm)],[c_727,c_5]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_1,plain,
% 51.52/7.02      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 51.52/7.02      inference(cnf_transformation,[],[f29]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_826,plain,
% 51.52/7.02      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 51.52/7.02      inference(superposition,[status(thm)],[c_813,c_1]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_963,plain,
% 51.52/7.02      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 51.52/7.02      inference(superposition,[status(thm)],[c_826,c_727]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_9,plain,
% 51.52/7.02      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 51.52/7.02      inference(cnf_transformation,[],[f60]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_10,plain,
% 51.52/7.02      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 51.52/7.02      inference(cnf_transformation,[],[f39]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_104,plain,
% 51.52/7.02      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 51.52/7.02      inference(theory_normalisation,[status(thm)],[c_9,c_10,c_1]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_967,plain,
% 51.52/7.02      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),X0)))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
% 51.52/7.02      inference(superposition,[status(thm)],[c_826,c_104]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_975,plain,
% 51.52/7.02      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),X0)))) = k3_xboole_0(k1_xboole_0,X0) ),
% 51.52/7.02      inference(demodulation,[status(thm)],[c_967,c_826]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_976,plain,
% 51.52/7.02      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(X0,X0)))) = k3_xboole_0(k1_xboole_0,X0) ),
% 51.52/7.02      inference(light_normalisation,[status(thm)],[c_975,c_8]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_594,plain,
% 51.52/7.02      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1)) = k5_xboole_0(X0,X1) ),
% 51.52/7.02      inference(superposition,[status(thm)],[c_8,c_10]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_977,plain,
% 51.52/7.02      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_xboole_0(k1_xboole_0,X0) ),
% 51.52/7.02      inference(demodulation,[status(thm)],[c_976,c_594,c_826]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_980,plain,
% 51.52/7.02      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 51.52/7.02      inference(demodulation,[status(thm)],[c_963,c_977]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_1110,plain,
% 51.52/7.02      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 51.52/7.02      inference(superposition,[status(thm)],[c_980,c_10]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_1116,plain,
% 51.52/7.02      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),X1)) = X1 ),
% 51.52/7.02      inference(demodulation,[status(thm)],[c_1110,c_826]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_1545,plain,
% 51.52/7.02      ( k3_xboole_0(k3_xboole_0(X0,X0),X0) = X0 ),
% 51.52/7.02      inference(superposition,[status(thm)],[c_1116,c_6]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_1584,plain,
% 51.52/7.02      ( k5_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X0)))) = k3_xboole_0(X0,X0) ),
% 51.52/7.02      inference(superposition,[status(thm)],[c_1545,c_6]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_1587,plain,
% 51.52/7.02      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),X0)),k3_xboole_0(X0,X0))))) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X0))) ),
% 51.52/7.02      inference(superposition,[status(thm)],[c_1545,c_104]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_1589,plain,
% 51.52/7.02      ( k3_xboole_0(X0,k3_xboole_0(X0,X0)) = X0 ),
% 51.52/7.02      inference(superposition,[status(thm)],[c_1545,c_0]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_1591,plain,
% 51.52/7.02      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),X0)),k3_xboole_0(X0,X0))))) = k5_xboole_0(X0,X0) ),
% 51.52/7.02      inference(demodulation,[status(thm)],[c_1587,c_1589]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_192,plain,
% 51.52/7.02      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 51.52/7.02      inference(superposition,[status(thm)],[c_10,c_1]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_1417,plain,
% 51.52/7.02      ( k5_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(X0,X1)) = k5_xboole_0(X1,k1_xboole_0) ),
% 51.52/7.02      inference(superposition,[status(thm)],[c_980,c_192]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_1420,plain,
% 51.52/7.02      ( k5_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(X0,X1)) = X1 ),
% 51.52/7.02      inference(demodulation,[status(thm)],[c_1417,c_813]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_1592,plain,
% 51.52/7.02      ( k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),X0)),k3_xboole_0(X0,X0))) = k5_xboole_0(X0,X0) ),
% 51.52/7.02      inference(demodulation,[status(thm)],[c_1591,c_1116,c_1420]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_1593,plain,
% 51.52/7.02      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X0))) = k5_xboole_0(X0,X0) ),
% 51.52/7.02      inference(demodulation,[status(thm)],[c_1592,c_1116]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_1594,plain,
% 51.52/7.02      ( k5_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(X0,X0)) = k3_xboole_0(X0,X0) ),
% 51.52/7.02      inference(demodulation,[status(thm)],[c_1584,c_1593]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_1595,plain,
% 51.52/7.02      ( k3_xboole_0(X0,X0) = X0 ),
% 51.52/7.02      inference(demodulation,[status(thm)],[c_1594,c_1420]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_1715,plain,
% 51.52/7.02      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 51.52/7.02      inference(demodulation,[status(thm)],[c_1595,c_980]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_193,plain,
% 51.52/7.02      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 51.52/7.02      inference(superposition,[status(thm)],[c_10,c_1]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_1750,plain,
% 51.52/7.02      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 51.52/7.02      inference(superposition,[status(thm)],[c_1715,c_193]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_1752,plain,
% 51.52/7.02      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 51.52/7.02      inference(demodulation,[status(thm)],[c_1750,c_813]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_176628,plain,
% 51.52/7.02      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
% 51.52/7.02      inference(demodulation,[status(thm)],[c_176627,c_1752]) ).
% 51.52/7.02  
% 51.52/7.02  cnf(c_176629,plain,
% 51.52/7.02      ( $false ),
% 51.52/7.02      inference(equality_resolution_simp,[status(thm)],[c_176628]) ).
% 51.52/7.02  
% 51.52/7.02  
% 51.52/7.02  % SZS output end CNFRefutation for theBenchmark.p
% 51.52/7.02  
% 51.52/7.02  ------                               Statistics
% 51.52/7.02  
% 51.52/7.02  ------ General
% 51.52/7.02  
% 51.52/7.02  abstr_ref_over_cycles:                  0
% 51.52/7.02  abstr_ref_under_cycles:                 0
% 51.52/7.02  gc_basic_clause_elim:                   0
% 51.52/7.02  forced_gc_time:                         0
% 51.52/7.02  parsing_time:                           0.009
% 51.52/7.02  unif_index_cands_time:                  0.
% 51.52/7.02  unif_index_add_time:                    0.
% 51.52/7.02  orderings_time:                         0.
% 51.52/7.02  out_proof_time:                         0.009
% 51.52/7.02  total_time:                             6.289
% 51.52/7.02  num_of_symbols:                         38
% 51.52/7.02  num_of_terms:                           395399
% 51.52/7.02  
% 51.52/7.02  ------ Preprocessing
% 51.52/7.02  
% 51.52/7.02  num_of_splits:                          0
% 51.52/7.02  num_of_split_atoms:                     0
% 51.52/7.02  num_of_reused_defs:                     0
% 51.52/7.02  num_eq_ax_congr_red:                    0
% 51.52/7.02  num_of_sem_filtered_clauses:            1
% 51.52/7.02  num_of_subtypes:                        0
% 51.52/7.02  monotx_restored_types:                  0
% 51.52/7.02  sat_num_of_epr_types:                   0
% 51.52/7.02  sat_num_of_non_cyclic_types:            0
% 51.52/7.02  sat_guarded_non_collapsed_types:        0
% 51.52/7.02  num_pure_diseq_elim:                    0
% 51.52/7.02  simp_replaced_by:                       0
% 51.52/7.02  res_preprocessed:                       61
% 51.52/7.02  prep_upred:                             0
% 51.52/7.02  prep_unflattend:                        0
% 51.52/7.02  smt_new_axioms:                         0
% 51.52/7.02  pred_elim_cands:                        1
% 51.52/7.02  pred_elim:                              0
% 51.52/7.02  pred_elim_cl:                           0
% 51.52/7.02  pred_elim_cycles:                       2
% 51.52/7.02  merged_defs:                            0
% 51.52/7.02  merged_defs_ncl:                        0
% 51.52/7.02  bin_hyper_res:                          0
% 51.52/7.02  prep_cycles:                            4
% 51.52/7.02  pred_elim_time:                         0.
% 51.52/7.02  splitting_time:                         0.
% 51.52/7.02  sem_filter_time:                        0.
% 51.52/7.02  monotx_time:                            0.001
% 51.52/7.02  subtype_inf_time:                       0.
% 51.52/7.02  
% 51.52/7.02  ------ Problem properties
% 51.52/7.02  
% 51.52/7.02  clauses:                                12
% 51.52/7.02  conjectures:                            1
% 51.52/7.02  epr:                                    2
% 51.52/7.02  horn:                                   12
% 51.52/7.02  ground:                                 1
% 51.52/7.02  unary:                                  10
% 51.52/7.02  binary:                                 1
% 51.52/7.02  lits:                                   15
% 51.52/7.02  lits_eq:                                10
% 51.52/7.02  fd_pure:                                0
% 51.52/7.02  fd_pseudo:                              0
% 51.52/7.02  fd_cond:                                0
% 51.52/7.02  fd_pseudo_cond:                         1
% 51.52/7.02  ac_symbols:                             1
% 51.52/7.02  
% 51.52/7.02  ------ Propositional Solver
% 51.52/7.02  
% 51.52/7.02  prop_solver_calls:                      35
% 51.52/7.02  prop_fast_solver_calls:                 634
% 51.52/7.02  smt_solver_calls:                       0
% 51.52/7.02  smt_fast_solver_calls:                  0
% 51.52/7.02  prop_num_of_clauses:                    21132
% 51.52/7.02  prop_preprocess_simplified:             28419
% 51.52/7.02  prop_fo_subsumed:                       0
% 51.52/7.02  prop_solver_time:                       0.
% 51.52/7.02  smt_solver_time:                        0.
% 51.52/7.02  smt_fast_solver_time:                   0.
% 51.52/7.02  prop_fast_solver_time:                  0.
% 51.52/7.02  prop_unsat_core_time:                   0.
% 51.52/7.02  
% 51.52/7.02  ------ QBF
% 51.52/7.02  
% 51.52/7.02  qbf_q_res:                              0
% 51.52/7.02  qbf_num_tautologies:                    0
% 51.52/7.02  qbf_prep_cycles:                        0
% 51.52/7.02  
% 51.52/7.02  ------ BMC1
% 51.52/7.02  
% 51.52/7.02  bmc1_current_bound:                     -1
% 51.52/7.02  bmc1_last_solved_bound:                 -1
% 51.52/7.02  bmc1_unsat_core_size:                   -1
% 51.52/7.02  bmc1_unsat_core_parents_size:           -1
% 51.52/7.02  bmc1_merge_next_fun:                    0
% 51.52/7.02  bmc1_unsat_core_clauses_time:           0.
% 51.52/7.02  
% 51.52/7.02  ------ Instantiation
% 51.52/7.02  
% 51.52/7.02  inst_num_of_clauses:                    3765
% 51.52/7.02  inst_num_in_passive:                    2049
% 51.52/7.02  inst_num_in_active:                     1239
% 51.52/7.02  inst_num_in_unprocessed:                477
% 51.52/7.02  inst_num_of_loops:                      1310
% 51.52/7.02  inst_num_of_learning_restarts:          0
% 51.52/7.02  inst_num_moves_active_passive:          67
% 51.52/7.02  inst_lit_activity:                      0
% 51.52/7.02  inst_lit_activity_moves:                1
% 51.52/7.02  inst_num_tautologies:                   0
% 51.52/7.02  inst_num_prop_implied:                  0
% 51.52/7.02  inst_num_existing_simplified:           0
% 51.52/7.02  inst_num_eq_res_simplified:             0
% 51.52/7.02  inst_num_child_elim:                    0
% 51.52/7.02  inst_num_of_dismatching_blockings:      1789
% 51.52/7.02  inst_num_of_non_proper_insts:           5517
% 51.52/7.02  inst_num_of_duplicates:                 0
% 51.52/7.02  inst_inst_num_from_inst_to_res:         0
% 51.52/7.02  inst_dismatching_checking_time:         0.
% 51.52/7.02  
% 51.52/7.02  ------ Resolution
% 51.52/7.02  
% 51.52/7.02  res_num_of_clauses:                     0
% 51.52/7.02  res_num_in_passive:                     0
% 51.52/7.02  res_num_in_active:                      0
% 51.52/7.02  res_num_of_loops:                       65
% 51.52/7.02  res_forward_subset_subsumed:            1692
% 51.52/7.02  res_backward_subset_subsumed:           0
% 51.52/7.02  res_forward_subsumed:                   0
% 51.52/7.02  res_backward_subsumed:                  0
% 51.52/7.02  res_forward_subsumption_resolution:     0
% 51.52/7.02  res_backward_subsumption_resolution:    0
% 51.52/7.02  res_clause_to_clause_subsumption:       644212
% 51.52/7.02  res_orphan_elimination:                 0
% 51.52/7.02  res_tautology_del:                      316
% 51.52/7.02  res_num_eq_res_simplified:              0
% 51.52/7.02  res_num_sel_changes:                    0
% 51.52/7.02  res_moves_from_active_to_pass:          0
% 51.52/7.02  
% 51.52/7.02  ------ Superposition
% 51.52/7.02  
% 51.52/7.02  sup_time_total:                         0.
% 51.52/7.02  sup_time_generating:                    0.
% 51.52/7.02  sup_time_sim_full:                      0.
% 51.52/7.02  sup_time_sim_immed:                     0.
% 51.52/7.02  
% 51.52/7.02  sup_num_of_clauses:                     9591
% 51.52/7.02  sup_num_in_active:                      222
% 51.52/7.02  sup_num_in_passive:                     9369
% 51.52/7.02  sup_num_of_loops:                       261
% 51.52/7.02  sup_fw_superposition:                   49906
% 51.52/7.02  sup_bw_superposition:                   36311
% 51.52/7.02  sup_immediate_simplified:               54297
% 51.52/7.02  sup_given_eliminated:                   10
% 51.52/7.02  comparisons_done:                       0
% 51.52/7.02  comparisons_avoided:                    0
% 51.52/7.02  
% 51.52/7.02  ------ Simplifications
% 51.52/7.02  
% 51.52/7.02  
% 51.52/7.02  sim_fw_subset_subsumed:                 0
% 51.52/7.02  sim_bw_subset_subsumed:                 0
% 51.52/7.02  sim_fw_subsumed:                        2685
% 51.52/7.02  sim_bw_subsumed:                        67
% 51.52/7.02  sim_fw_subsumption_res:                 0
% 51.52/7.02  sim_bw_subsumption_res:                 0
% 51.52/7.02  sim_tautology_del:                      0
% 51.52/7.02  sim_eq_tautology_del:                   12513
% 51.52/7.02  sim_eq_res_simp:                        0
% 51.52/7.02  sim_fw_demodulated:                     50541
% 51.52/7.02  sim_bw_demodulated:                     345
% 51.52/7.02  sim_light_normalised:                   14329
% 51.52/7.02  sim_joinable_taut:                      1681
% 51.52/7.02  sim_joinable_simp:                      0
% 51.52/7.02  sim_ac_normalised:                      0
% 51.52/7.02  sim_smt_subsumption:                    0
% 51.52/7.02  
%------------------------------------------------------------------------------
