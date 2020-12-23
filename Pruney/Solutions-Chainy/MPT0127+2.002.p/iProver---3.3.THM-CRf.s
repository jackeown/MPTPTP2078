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
% DateTime   : Thu Dec  3 11:26:16 EST 2020

% Result     : Theorem 43.27s
% Output     : CNFRefutation 43.27s
% Verified   : 
% Statistics : Number of formulae       :  178 (326122 expanded)
%              Number of clauses        :  136 (98212 expanded)
%              Number of leaves         :   15 (84934 expanded)
%              Depth                    :   47
%              Number of atoms          :  186 (364056 expanded)
%              Number of equality atoms :  177 (320703 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    9 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f8])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f41,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k5_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(X1,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f23,f38,f38])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f24,f34])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)),k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f27,f38,f34])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),X2) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X2)),k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X0))) ),
    inference(definition_unfolding,[],[f26,f38,f38])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f25,f34,f34])).

fof(f15,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2) ),
    inference(negated_conjecture,[],[f15])).

fof(f20,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) != k1_enumset1(X0,X1,X2) ),
    inference(ennf_transformation,[],[f16])).

fof(f21,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) != k1_enumset1(X0,X1,X2)
   => k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)) != k1_enumset1(sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)) != k1_enumset1(sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f21])).

fof(f37,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)) != k1_enumset1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f35,f34])).

fof(f40,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f36,f34,f39])).

fof(f46,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))) ),
    inference(definition_unfolding,[],[f37,f34,f39,f40])).

cnf(c_6,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_47,plain,
    ( X0 != X1
    | k4_xboole_0(X2,X1) != X3
    | k4_xboole_0(X3,X0) = X3 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_7])).

cnf(c_48,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(unflattening,[status(thm)],[c_47])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k5_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(X1,k4_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_8,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_6102,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(X1,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_0,c_8])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_5942,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X0),X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_8])).

cnf(c_5956,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)),X2))) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_5942,c_8])).

cnf(c_5962,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)),X2))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_5956,c_8])).

cnf(c_6741,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X1,X2))),X3)))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) ),
    inference(superposition,[status(thm)],[c_8,c_5962])).

cnf(c_6794,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(k5_xboole_0(X0,X1),X2)),X3)))) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) ),
    inference(superposition,[status(thm)],[c_5962,c_8])).

cnf(c_6835,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X1,X2))),X3)))) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) ),
    inference(light_normalisation,[status(thm)],[c_6794,c_8])).

cnf(c_6909,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) ),
    inference(demodulation,[status(thm)],[c_6741,c_6835])).

cnf(c_7501,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) ),
    inference(superposition,[status(thm)],[c_6909,c_8])).

cnf(c_7561,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) ),
    inference(demodulation,[status(thm)],[c_7501,c_6909])).

cnf(c_10585,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_6102,c_7561])).

cnf(c_4,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)),k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X2)),k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X0))) = k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_6247,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X0),k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(superposition,[status(thm)],[c_4,c_3])).

cnf(c_123053,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))))),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(demodulation,[status(thm)],[c_6247,c_7561])).

cnf(c_123065,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X0)))),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(superposition,[status(thm)],[c_10585,c_123053])).

cnf(c_6178,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X0)))) = k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),X2) ),
    inference(superposition,[status(thm)],[c_3,c_8])).

cnf(c_91392,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X0)))) = k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X1,X0)))),X2) ),
    inference(demodulation,[status(thm)],[c_6178,c_7561])).

cnf(c_123698,plain,
    ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,X0)))),X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(demodulation,[status(thm)],[c_123065,c_91392])).

cnf(c_6163,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,k4_xboole_0(X0,X0))),X0) = k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X0),X0))) ),
    inference(superposition,[status(thm)],[c_1,c_3])).

cnf(c_6213,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X0),X0))) = k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),X0),X0) ),
    inference(light_normalisation,[status(thm)],[c_6163,c_1])).

cnf(c_6214,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),X0),X0) = k5_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_6213,c_1,c_48])).

cnf(c_6320,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,X0)),X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_8,c_6214])).

cnf(c_91613,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X0,X1))))) = k4_xboole_0(k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X2,k4_xboole_0(X0,X2)))),X1) ),
    inference(superposition,[status(thm)],[c_91392,c_10585])).

cnf(c_2,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_6237,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X0)),X1)) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X1))) ),
    inference(superposition,[status(thm)],[c_2,c_4])).

cnf(c_6268,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X1))) ),
    inference(light_normalisation,[status(thm)],[c_6237,c_1])).

cnf(c_6269,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_6268,c_1])).

cnf(c_6594,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)),k5_xboole_0(k4_xboole_0(X0,X1),X2)) = k5_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_6269,c_8])).

cnf(c_14316,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X2),X3)) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X2),X3) ),
    inference(superposition,[status(thm)],[c_6594,c_8])).

cnf(c_7476,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X2,X2))) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_1,c_6909])).

cnf(c_7744,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X2,X2))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_7476,c_8])).

cnf(c_6327,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),X0),X0) = k4_xboole_0(k5_xboole_0(X0,X0),X0) ),
    inference(superposition,[status(thm)],[c_6214,c_48])).

cnf(c_6339,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X0),X0) = k5_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_6327,c_6214])).

cnf(c_6590,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0)),k5_xboole_0(X0,X0)) = k4_xboole_0(k5_xboole_0(X0,X0),X0) ),
    inference(superposition,[status(thm)],[c_6339,c_6269])).

cnf(c_6618,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0)),k5_xboole_0(X0,X0)) = k5_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_6590,c_6339])).

cnf(c_7406,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X0))),k5_xboole_0(X0,X0)) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_8,c_6618])).

cnf(c_8026,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X0))),k5_xboole_0(k5_xboole_0(X0,X0),X1)) = k5_xboole_0(k5_xboole_0(X0,X0),X1) ),
    inference(superposition,[status(thm)],[c_7406,c_8])).

cnf(c_17287,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X0))),k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X2,X2))) ),
    inference(superposition,[status(thm)],[c_7744,c_8026])).

cnf(c_17574,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X2,X2))) = k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_17287,c_8026])).

cnf(c_17576,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X2,X2))) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_17574,c_7561])).

cnf(c_58939,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,X1),X2))) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X2,X2)) ),
    inference(superposition,[status(thm)],[c_14316,c_17576])).

cnf(c_6597,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_6269,c_8])).

cnf(c_8445,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X2,X2)),X3)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_7744,c_8])).

cnf(c_5955,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X0),X1),X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_5942,c_8])).

cnf(c_5965,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X0),X1),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_5955,c_8])).

cnf(c_8465,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X2,X2)),X3)) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X0),k5_xboole_0(X1,X2)),X3)) ),
    inference(superposition,[status(thm)],[c_7744,c_5965])).

cnf(c_8488,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X2,X2)),X3)) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_8465,c_5965,c_7501])).

cnf(c_8527,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3) ),
    inference(light_normalisation,[status(thm)],[c_8445,c_8488])).

cnf(c_9067,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,X1),X2))) = k5_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_6597,c_8527])).

cnf(c_58953,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X2,X2)) = k5_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_58939,c_9067])).

cnf(c_59927,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X2),k5_xboole_0(k4_xboole_0(X2,X2),X3)) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X2),X3) ),
    inference(superposition,[status(thm)],[c_58953,c_8])).

cnf(c_65024,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X0),X0),k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X0),X0),X0)),k5_xboole_0(k4_xboole_0(X0,X0),X0)) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X0),X0),k5_xboole_0(k4_xboole_0(X0,X0),X0)) ),
    inference(superposition,[status(thm)],[c_59927,c_6320])).

cnf(c_65250,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X0),X0),k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X0),X0),X0)),k5_xboole_0(k4_xboole_0(X0,X0),X0)) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X0),X0),X0) ),
    inference(demodulation,[status(thm)],[c_65024,c_59927])).

cnf(c_65252,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X0),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X0),X0),X0))),k5_xboole_0(k4_xboole_0(X0,X0),X0)) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X0),X0),X0) ),
    inference(demodulation,[status(thm)],[c_65250,c_7561])).

cnf(c_5953,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0))) = k5_xboole_0(X0,k4_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_1,c_5942])).

cnf(c_5968,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5953,c_1])).

cnf(c_6166,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X0)),k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X0),X0))),k4_xboole_0(X0,X0)) = k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)),X0))) ),
    inference(superposition,[status(thm)],[c_5968,c_3])).

cnf(c_6199,plain,
    ( k4_xboole_0(k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,k4_xboole_0(X0,X0))),X0),k4_xboole_0(X0,X0)) = k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)),X0))) ),
    inference(demodulation,[status(thm)],[c_6166,c_3])).

cnf(c_6171,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),X0) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_48,c_3])).

cnf(c_6200,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X0)),k5_xboole_0(X0,k4_xboole_0(X0,X0))),k4_xboole_0(X0,X0)) = k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)),X0))) ),
    inference(demodulation,[status(thm)],[c_6199,c_6171])).

cnf(c_6202,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)),X0))) = k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(X0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_6200,c_1])).

cnf(c_6599,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_6269,c_6214])).

cnf(c_23816,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)),X0))) = k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(X0,X0)) ),
    inference(demodulation,[status(thm)],[c_6202,c_6599])).

cnf(c_6369,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,X1),X0)),X1) ),
    inference(superposition,[status(thm)],[c_6339,c_2])).

cnf(c_24185,plain,
    ( k5_xboole_0(k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0))),X0),k5_xboole_0(k4_xboole_0(k5_xboole_0(X0,X0),X0),k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k5_xboole_0(X0,X0),X0)),k4_xboole_0(k5_xboole_0(X0,X0),X0)))) = k4_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,X0),X0),X0))) ),
    inference(superposition,[status(thm)],[c_6369,c_4])).

cnf(c_7002,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0))) = k4_xboole_0(k5_xboole_0(X0,X0),X0) ),
    inference(superposition,[status(thm)],[c_6339,c_6597])).

cnf(c_7028,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0))) = k5_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_7002,c_6339])).

cnf(c_7602,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X0)))) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_8,c_7028])).

cnf(c_7298,plain,
    ( k5_xboole_0(k4_xboole_0(k5_xboole_0(X0,X0),X0),k4_xboole_0(k5_xboole_0(X0,X0),X0)) = k4_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_6339,c_6599])).

cnf(c_7374,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0)) = k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_7298,c_6339])).

cnf(c_8648,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0)) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X0))) ),
    inference(demodulation,[status(thm)],[c_7561,c_7374])).

cnf(c_10527,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,X0)))) = k5_xboole_0(k5_xboole_0(X0,X0),X0) ),
    inference(superposition,[status(thm)],[c_1,c_6102])).

cnf(c_10725,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X0)) = k5_xboole_0(k5_xboole_0(X0,X0),X0) ),
    inference(light_normalisation,[status(thm)],[c_10527,c_1])).

cnf(c_6359,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_8,c_6339])).

cnf(c_13084,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))),k5_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_6359,c_7561])).

cnf(c_13163,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X0)))),k5_xboole_0(X0,k5_xboole_0(X0,X0))) = k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X0),X0))) ),
    inference(superposition,[status(thm)],[c_10725,c_13084])).

cnf(c_13290,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,k5_xboole_0(X0,X0))) = k5_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_13163,c_7602,c_10725])).

cnf(c_24261,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X0))),k5_xboole_0(X0,X0)))) = k5_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_24185,c_6339,c_7602,c_8648,c_13290])).

cnf(c_17354,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X0))),k5_xboole_0(X0,X0)) = k5_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_8026,c_7744])).

cnf(c_17356,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = k5_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_17354,c_7406])).

cnf(c_17334,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X0))),k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),X1),X2) ),
    inference(superposition,[status(thm)],[c_8026,c_8527])).

cnf(c_17407,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),X1),X2) = k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_17334,c_8026])).

cnf(c_17409,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),X1),X2) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_17407,c_7561])).

cnf(c_18001,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X0),X1))) = k5_xboole_0(k5_xboole_0(X0,X0),X1) ),
    inference(superposition,[status(thm)],[c_17356,c_17409])).

cnf(c_18537,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_18001,c_5942])).

cnf(c_24262,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X0))),k5_xboole_0(X0,X0)))))) = k5_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_24261,c_18537])).

cnf(c_8353,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X0))))) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_7602,c_8])).

cnf(c_24263,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X0))) = k5_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_24262,c_8353,c_13084])).

cnf(c_18565,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,X1)),X2) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_18537,c_17409])).

cnf(c_25279,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X0),X1))) = k5_xboole_0(k5_xboole_0(X0,X0),X1) ),
    inference(superposition,[status(thm)],[c_24263,c_18565])).

cnf(c_25314,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X1)))) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_25279,c_18537])).

cnf(c_26067,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)),X0))) = k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(X0,X0)))) ),
    inference(superposition,[status(thm)],[c_23816,c_25314])).

cnf(c_6130,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X0))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0)) ),
    inference(superposition,[status(thm)],[c_2,c_5942])).

cnf(c_11768,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,X0),X0),k4_xboole_0(X0,X0))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,X0)),X0)) ),
    inference(superposition,[status(thm)],[c_6339,c_6130])).

cnf(c_11871,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(X0,X0))) = k5_xboole_0(X0,k5_xboole_0(X0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_11768,c_6320,c_6339])).

cnf(c_26535,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = k5_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_26067,c_11871,c_23816,c_24263])).

cnf(c_26667,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,X0),X0)),X0) = k5_xboole_0(k4_xboole_0(X0,X0),k5_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_26535,c_6369])).

cnf(c_26669,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X0),k5_xboole_0(X0,X0)) = k5_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_26667,c_6320,c_6339])).

cnf(c_26835,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X0),k5_xboole_0(X0,k5_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,X0),X1) ),
    inference(superposition,[status(thm)],[c_26669,c_8527])).

cnf(c_26877,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X0),k5_xboole_0(X0,k5_xboole_0(X0,X1))) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_26835,c_18537])).

cnf(c_6321,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))),k5_xboole_0(X0,X1)),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_8,c_6214])).

cnf(c_8125,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),X4) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),X3),X4)) ),
    inference(superposition,[status(thm)],[c_7501,c_8])).

cnf(c_8214,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X4)))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),X4) ),
    inference(demodulation,[status(thm)],[c_8125,c_7501])).

cnf(c_33712,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))))),k5_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_6321,c_7561,c_8214])).

cnf(c_33776,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X0),k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X0),k5_xboole_0(X0,X0)))),k5_xboole_0(k4_xboole_0(X0,X0),X0)) = k5_xboole_0(k4_xboole_0(X0,X0),k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X0),X0))) ),
    inference(superposition,[status(thm)],[c_5942,c_33712])).

cnf(c_34438,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X0),k5_xboole_0(X0,k5_xboole_0(X0,X0))),k5_xboole_0(k4_xboole_0(X0,X0),X0)) = k5_xboole_0(k4_xboole_0(X0,X0),k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X0),X0))) ),
    inference(light_normalisation,[status(thm)],[c_33776,c_26669])).

cnf(c_34439,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,X0)),k5_xboole_0(k4_xboole_0(X0,X0),X0)) = k5_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_34438,c_5942,c_26669,c_26877])).

cnf(c_65253,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X0),X0),X0) = k5_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_65252,c_5965,c_26877,c_34439])).

cnf(c_67306,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X0),X0),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X0),X1) ),
    inference(superposition,[status(thm)],[c_65253,c_8])).

cnf(c_67474,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X0),X0),k5_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_67306,c_18537])).

cnf(c_91682,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)),k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)))))),X1) = k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)))))) ),
    inference(superposition,[status(thm)],[c_91392,c_67474])).

cnf(c_91684,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))))),X1) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_91682,c_6269,c_6597,c_6599])).

cnf(c_91935,plain,
    ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,X0)))),X1),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_91613,c_91684])).

cnf(c_91938,plain,
    ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,X0)),X1),X1) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_91935,c_1])).

cnf(c_92598,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X0),X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_6320,c_91938])).

cnf(c_93047,plain,
    ( k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_92598,c_6339])).

cnf(c_94061,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_93047,c_1])).

cnf(c_123699,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_123698,c_93047,c_94061])).

cnf(c_127195,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(superposition,[status(thm)],[c_48,c_123699])).

cnf(c_127759,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_127195,c_123699])).

cnf(c_129757,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X1),X0)) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1) ),
    inference(demodulation,[status(thm)],[c_127759,c_2])).

cnf(c_10,negated_conjecture,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_5940,plain,
    ( k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k4_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))) ),
    inference(demodulation,[status(thm)],[c_8,c_10])).

cnf(c_127148,plain,
    ( k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1)))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))) ),
    inference(demodulation,[status(thm)],[c_123699,c_5940])).

cnf(c_131447,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))) ),
    inference(demodulation,[status(thm)],[c_129757,c_127148])).

cnf(c_59,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_7593,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))) = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))) ),
    inference(instantiation,[status(thm)],[c_59])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_131447,c_7593])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:43:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 43.27/6.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 43.27/6.00  
% 43.27/6.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 43.27/6.00  
% 43.27/6.00  ------  iProver source info
% 43.27/6.00  
% 43.27/6.00  git: date: 2020-06-30 10:37:57 +0100
% 43.27/6.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 43.27/6.00  git: non_committed_changes: false
% 43.27/6.00  git: last_make_outside_of_git: false
% 43.27/6.00  
% 43.27/6.00  ------ 
% 43.27/6.00  ------ Parsing...
% 43.27/6.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 43.27/6.00  
% 43.27/6.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 43.27/6.00  
% 43.27/6.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 43.27/6.00  
% 43.27/6.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.27/6.00  ------ Proving...
% 43.27/6.00  ------ Problem Properties 
% 43.27/6.00  
% 43.27/6.00  
% 43.27/6.00  clauses                                 10
% 43.27/6.00  conjectures                             1
% 43.27/6.00  EPR                                     0
% 43.27/6.00  Horn                                    10
% 43.27/6.00  unary                                   10
% 43.27/6.00  binary                                  0
% 43.27/6.00  lits                                    10
% 43.27/6.00  lits eq                                 10
% 43.27/6.00  fd_pure                                 0
% 43.27/6.00  fd_pseudo                               0
% 43.27/6.00  fd_cond                                 0
% 43.27/6.00  fd_pseudo_cond                          0
% 43.27/6.00  AC symbols                              0
% 43.27/6.00  
% 43.27/6.00  ------ Input Options Time Limit: Unbounded
% 43.27/6.00  
% 43.27/6.00  
% 43.27/6.00  
% 43.27/6.00  
% 43.27/6.00  ------ Preprocessing...
% 43.27/6.00  
% 43.27/6.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 43.27/6.00  Current options:
% 43.27/6.00  ------ 
% 43.27/6.00  
% 43.27/6.00  
% 43.27/6.00  
% 43.27/6.00  
% 43.27/6.00  ------ Proving...
% 43.27/6.00  
% 43.27/6.00  
% 43.27/6.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.27/6.00  
% 43.27/6.00  ------ Proving...
% 43.27/6.00  
% 43.27/6.00  
% 43.27/6.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.27/6.00  
% 43.27/6.00  ------ Proving...
% 43.27/6.00  
% 43.27/6.00  
% 43.27/6.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.27/6.00  
% 43.27/6.00  ------ Proving...
% 43.27/6.00  
% 43.27/6.00  
% 43.27/6.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.27/6.00  
% 43.27/6.00  ------ Proving...
% 43.27/6.00  
% 43.27/6.00  
% 43.27/6.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.27/6.00  
% 43.27/6.00  ------ Proving...
% 43.27/6.00  
% 43.27/6.00  
% 43.27/6.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.27/6.00  
% 43.27/6.00  ------ Proving...
% 43.27/6.00  
% 43.27/6.00  
% 43.27/6.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.27/6.00  
% 43.27/6.00  ------ Proving...
% 43.27/6.00  
% 43.27/6.00  
% 43.27/6.00  % SZS status Theorem for theBenchmark.p
% 43.27/6.00  
% 43.27/6.00  % SZS output start CNFRefutation for theBenchmark.p
% 43.27/6.00  
% 43.27/6.00  fof(f7,axiom,(
% 43.27/6.00    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 43.27/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.27/6.00  
% 43.27/6.00  fof(f29,plain,(
% 43.27/6.00    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 43.27/6.00    inference(cnf_transformation,[],[f7])).
% 43.27/6.00  
% 43.27/6.00  fof(f8,axiom,(
% 43.27/6.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 43.27/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.27/6.00  
% 43.27/6.00  fof(f18,plain,(
% 43.27/6.00    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 43.27/6.00    inference(unused_predicate_definition_removal,[],[f8])).
% 43.27/6.00  
% 43.27/6.00  fof(f19,plain,(
% 43.27/6.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 43.27/6.00    inference(ennf_transformation,[],[f18])).
% 43.27/6.00  
% 43.27/6.00  fof(f30,plain,(
% 43.27/6.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 43.27/6.00    inference(cnf_transformation,[],[f19])).
% 43.27/6.00  
% 43.27/6.00  fof(f1,axiom,(
% 43.27/6.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 43.27/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.27/6.00  
% 43.27/6.00  fof(f23,plain,(
% 43.27/6.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 43.27/6.00    inference(cnf_transformation,[],[f1])).
% 43.27/6.00  
% 43.27/6.00  fof(f11,axiom,(
% 43.27/6.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 43.27/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.27/6.00  
% 43.27/6.00  fof(f33,plain,(
% 43.27/6.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 43.27/6.00    inference(cnf_transformation,[],[f11])).
% 43.27/6.00  
% 43.27/6.00  fof(f12,axiom,(
% 43.27/6.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 43.27/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.27/6.00  
% 43.27/6.00  fof(f34,plain,(
% 43.27/6.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 43.27/6.00    inference(cnf_transformation,[],[f12])).
% 43.27/6.00  
% 43.27/6.00  fof(f38,plain,(
% 43.27/6.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 43.27/6.00    inference(definition_unfolding,[],[f33,f34])).
% 43.27/6.00  
% 43.27/6.00  fof(f41,plain,(
% 43.27/6.00    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k5_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) )),
% 43.27/6.00    inference(definition_unfolding,[],[f23,f38,f38])).
% 43.27/6.00  
% 43.27/6.00  fof(f9,axiom,(
% 43.27/6.00    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 43.27/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.27/6.00  
% 43.27/6.00  fof(f31,plain,(
% 43.27/6.00    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 43.27/6.00    inference(cnf_transformation,[],[f9])).
% 43.27/6.00  
% 43.27/6.00  fof(f2,axiom,(
% 43.27/6.00    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 43.27/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.27/6.00  
% 43.27/6.00  fof(f17,plain,(
% 43.27/6.00    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 43.27/6.00    inference(rectify,[],[f2])).
% 43.27/6.00  
% 43.27/6.00  fof(f24,plain,(
% 43.27/6.00    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 43.27/6.00    inference(cnf_transformation,[],[f17])).
% 43.27/6.00  
% 43.27/6.00  fof(f42,plain,(
% 43.27/6.00    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 43.27/6.00    inference(definition_unfolding,[],[f24,f34])).
% 43.27/6.00  
% 43.27/6.00  fof(f5,axiom,(
% 43.27/6.00    ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 43.27/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.27/6.00  
% 43.27/6.00  fof(f27,plain,(
% 43.27/6.00    ( ! [X2,X0,X1] : (k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 43.27/6.00    inference(cnf_transformation,[],[f5])).
% 43.27/6.00  
% 43.27/6.00  fof(f45,plain,(
% 43.27/6.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)),k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X0,X1))))) )),
% 43.27/6.00    inference(definition_unfolding,[],[f27,f38,f34])).
% 43.27/6.00  
% 43.27/6.00  fof(f4,axiom,(
% 43.27/6.00    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 43.27/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.27/6.00  
% 43.27/6.00  fof(f26,plain,(
% 43.27/6.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 43.27/6.00    inference(cnf_transformation,[],[f4])).
% 43.27/6.00  
% 43.27/6.00  fof(f44,plain,(
% 43.27/6.00    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),X2) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X2)),k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X0)))) )),
% 43.27/6.00    inference(definition_unfolding,[],[f26,f38,f38])).
% 43.27/6.00  
% 43.27/6.00  fof(f3,axiom,(
% 43.27/6.00    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2)),
% 43.27/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.27/6.00  
% 43.27/6.00  fof(f25,plain,(
% 43.27/6.00    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 43.27/6.00    inference(cnf_transformation,[],[f3])).
% 43.27/6.00  
% 43.27/6.00  fof(f43,plain,(
% 43.27/6.00    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X0,X2)))) )),
% 43.27/6.00    inference(definition_unfolding,[],[f25,f34,f34])).
% 43.27/6.00  
% 43.27/6.00  fof(f15,conjecture,(
% 43.27/6.00    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2)),
% 43.27/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.27/6.00  
% 43.27/6.00  fof(f16,negated_conjecture,(
% 43.27/6.00    ~! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2)),
% 43.27/6.00    inference(negated_conjecture,[],[f15])).
% 43.27/6.00  
% 43.27/6.00  fof(f20,plain,(
% 43.27/6.00    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) != k1_enumset1(X0,X1,X2)),
% 43.27/6.00    inference(ennf_transformation,[],[f16])).
% 43.27/6.00  
% 43.27/6.00  fof(f21,plain,(
% 43.27/6.00    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) != k1_enumset1(X0,X1,X2) => k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)) != k1_enumset1(sK0,sK1,sK2)),
% 43.27/6.00    introduced(choice_axiom,[])).
% 43.27/6.00  
% 43.27/6.00  fof(f22,plain,(
% 43.27/6.00    k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)) != k1_enumset1(sK0,sK1,sK2)),
% 43.27/6.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f21])).
% 43.27/6.00  
% 43.27/6.00  fof(f37,plain,(
% 43.27/6.00    k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)) != k1_enumset1(sK0,sK1,sK2)),
% 43.27/6.00    inference(cnf_transformation,[],[f22])).
% 43.27/6.00  
% 43.27/6.00  fof(f14,axiom,(
% 43.27/6.00    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)),
% 43.27/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.27/6.00  
% 43.27/6.00  fof(f36,plain,(
% 43.27/6.00    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)) )),
% 43.27/6.00    inference(cnf_transformation,[],[f14])).
% 43.27/6.00  
% 43.27/6.00  fof(f13,axiom,(
% 43.27/6.00    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 43.27/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.27/6.00  
% 43.27/6.00  fof(f35,plain,(
% 43.27/6.00    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 43.27/6.00    inference(cnf_transformation,[],[f13])).
% 43.27/6.00  
% 43.27/6.00  fof(f39,plain,(
% 43.27/6.00    ( ! [X0,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = k2_tarski(X0,X1)) )),
% 43.27/6.00    inference(definition_unfolding,[],[f35,f34])).
% 43.27/6.00  
% 43.27/6.00  fof(f40,plain,(
% 43.27/6.00    ( ! [X2,X0,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))) = k1_enumset1(X0,X1,X2)) )),
% 43.27/6.00    inference(definition_unfolding,[],[f36,f34,f39])).
% 43.27/6.00  
% 43.27/6.00  fof(f46,plain,(
% 43.27/6.00    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))),
% 43.27/6.00    inference(definition_unfolding,[],[f37,f34,f39,f40])).
% 43.27/6.00  
% 43.27/6.00  cnf(c_6,plain,
% 43.27/6.00      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 43.27/6.00      inference(cnf_transformation,[],[f29]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_7,plain,
% 43.27/6.00      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 43.27/6.00      inference(cnf_transformation,[],[f30]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_47,plain,
% 43.27/6.00      ( X0 != X1 | k4_xboole_0(X2,X1) != X3 | k4_xboole_0(X3,X0) = X3 ),
% 43.27/6.00      inference(resolution_lifted,[status(thm)],[c_6,c_7]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_48,plain,
% 43.27/6.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 43.27/6.00      inference(unflattening,[status(thm)],[c_47]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_0,plain,
% 43.27/6.00      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k5_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(X1,k4_xboole_0(X0,X1))) ),
% 43.27/6.00      inference(cnf_transformation,[],[f41]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_8,plain,
% 43.27/6.00      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 43.27/6.00      inference(cnf_transformation,[],[f31]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_6102,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(X1,k4_xboole_0(X0,X1))) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_0,c_8]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_1,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 43.27/6.00      inference(cnf_transformation,[],[f42]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_5942,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X0),X1)) = k5_xboole_0(X0,X1) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_1,c_8]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_5956,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)),X2))) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_5942,c_8]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_5962,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)),X2))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 43.27/6.00      inference(light_normalisation,[status(thm)],[c_5956,c_8]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_6741,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X1,X2))),X3)))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_8,c_5962]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_6794,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(k5_xboole_0(X0,X1),X2)),X3)))) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_5962,c_8]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_6835,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X1,X2))),X3)))) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) ),
% 43.27/6.00      inference(light_normalisation,[status(thm)],[c_6794,c_8]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_6909,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) ),
% 43.27/6.00      inference(demodulation,[status(thm)],[c_6741,c_6835]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_7501,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_6909,c_8]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_7561,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) ),
% 43.27/6.00      inference(demodulation,[status(thm)],[c_7501,c_6909]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_10585,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_6102,c_7561]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_4,plain,
% 43.27/6.00      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)),k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
% 43.27/6.00      inference(cnf_transformation,[],[f45]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_3,plain,
% 43.27/6.00      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X2)),k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X0))) = k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),X2) ),
% 43.27/6.00      inference(cnf_transformation,[],[f44]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_6247,plain,
% 43.27/6.00      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X0),k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_4,c_3]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_123053,plain,
% 43.27/6.00      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))))),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
% 43.27/6.00      inference(demodulation,[status(thm)],[c_6247,c_7561]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_123065,plain,
% 43.27/6.00      ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X0)))),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_10585,c_123053]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_6178,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X0)))) = k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),X2) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_3,c_8]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_91392,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X0)))) = k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X1,X0)))),X2) ),
% 43.27/6.00      inference(demodulation,[status(thm)],[c_6178,c_7561]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_123698,plain,
% 43.27/6.00      ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,X0)))),X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
% 43.27/6.00      inference(demodulation,[status(thm)],[c_123065,c_91392]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_6163,plain,
% 43.27/6.00      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,k4_xboole_0(X0,X0))),X0) = k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X0),X0))) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_1,c_3]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_6213,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X0),X0))) = k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),X0),X0) ),
% 43.27/6.00      inference(light_normalisation,[status(thm)],[c_6163,c_1]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_6214,plain,
% 43.27/6.00      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),X0),X0) = k5_xboole_0(X0,X0) ),
% 43.27/6.00      inference(demodulation,[status(thm)],[c_6213,c_1,c_48]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_6320,plain,
% 43.27/6.00      ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,X0)),X0) = k5_xboole_0(X0,X0) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_8,c_6214]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_91613,plain,
% 43.27/6.00      ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X0,X1))))) = k4_xboole_0(k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X2,k4_xboole_0(X0,X2)))),X1) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_91392,c_10585]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_2,plain,
% 43.27/6.00      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1) ),
% 43.27/6.00      inference(cnf_transformation,[],[f43]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_6237,plain,
% 43.27/6.00      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X0)),X1)) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X1))) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_2,c_4]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_6268,plain,
% 43.27/6.00      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X1))) ),
% 43.27/6.00      inference(light_normalisation,[status(thm)],[c_6237,c_1]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_6269,plain,
% 43.27/6.00      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
% 43.27/6.00      inference(demodulation,[status(thm)],[c_6268,c_1]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_6594,plain,
% 43.27/6.00      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)),k5_xboole_0(k4_xboole_0(X0,X1),X2)) = k5_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_6269,c_8]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_14316,plain,
% 43.27/6.00      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X2),X3)) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X2),X3) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_6594,c_8]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_7476,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X2,X2))) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_1,c_6909]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_7744,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X2,X2))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 43.27/6.00      inference(light_normalisation,[status(thm)],[c_7476,c_8]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_6327,plain,
% 43.27/6.00      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),X0),X0) = k4_xboole_0(k5_xboole_0(X0,X0),X0) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_6214,c_48]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_6339,plain,
% 43.27/6.00      ( k4_xboole_0(k5_xboole_0(X0,X0),X0) = k5_xboole_0(X0,X0) ),
% 43.27/6.00      inference(light_normalisation,[status(thm)],[c_6327,c_6214]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_6590,plain,
% 43.27/6.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0)),k5_xboole_0(X0,X0)) = k4_xboole_0(k5_xboole_0(X0,X0),X0) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_6339,c_6269]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_6618,plain,
% 43.27/6.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0)),k5_xboole_0(X0,X0)) = k5_xboole_0(X0,X0) ),
% 43.27/6.00      inference(light_normalisation,[status(thm)],[c_6590,c_6339]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_7406,plain,
% 43.27/6.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X0))),k5_xboole_0(X0,X0)) = k5_xboole_0(X0,X0) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_8,c_6618]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_8026,plain,
% 43.27/6.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X0))),k5_xboole_0(k5_xboole_0(X0,X0),X1)) = k5_xboole_0(k5_xboole_0(X0,X0),X1) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_7406,c_8]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_17287,plain,
% 43.27/6.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X0))),k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X2,X2))) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_7744,c_8026]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_17574,plain,
% 43.27/6.00      ( k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X2,X2))) = k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X1,X2)) ),
% 43.27/6.00      inference(demodulation,[status(thm)],[c_17287,c_8026]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_17576,plain,
% 43.27/6.00      ( k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X2,X2))) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) ),
% 43.27/6.00      inference(demodulation,[status(thm)],[c_17574,c_7561]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_58939,plain,
% 43.27/6.00      ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,X1),X2))) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X2,X2)) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_14316,c_17576]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_6597,plain,
% 43.27/6.00      ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_6269,c_8]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_8445,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X2,X2)),X3)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_7744,c_8]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_5955,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X0),X1),X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_5942,c_8]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_5965,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X0),X1),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 43.27/6.00      inference(light_normalisation,[status(thm)],[c_5955,c_8]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_8465,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X2,X2)),X3)) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X0),k5_xboole_0(X1,X2)),X3)) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_7744,c_5965]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_8488,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X2,X2)),X3)) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))) ),
% 43.27/6.00      inference(demodulation,[status(thm)],[c_8465,c_5965,c_7501]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_8527,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3) ),
% 43.27/6.00      inference(light_normalisation,[status(thm)],[c_8445,c_8488]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_9067,plain,
% 43.27/6.00      ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,X1),X2))) = k5_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_6597,c_8527]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_58953,plain,
% 43.27/6.00      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X2,X2)) = k5_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 43.27/6.00      inference(light_normalisation,[status(thm)],[c_58939,c_9067]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_59927,plain,
% 43.27/6.00      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X2),k5_xboole_0(k4_xboole_0(X2,X2),X3)) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X2),X3) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_58953,c_8]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_65024,plain,
% 43.27/6.00      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X0),X0),k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X0),X0),X0)),k5_xboole_0(k4_xboole_0(X0,X0),X0)) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X0),X0),k5_xboole_0(k4_xboole_0(X0,X0),X0)) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_59927,c_6320]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_65250,plain,
% 43.27/6.00      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X0),X0),k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X0),X0),X0)),k5_xboole_0(k4_xboole_0(X0,X0),X0)) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X0),X0),X0) ),
% 43.27/6.00      inference(demodulation,[status(thm)],[c_65024,c_59927]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_65252,plain,
% 43.27/6.00      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X0),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X0),X0),X0))),k5_xboole_0(k4_xboole_0(X0,X0),X0)) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X0),X0),X0) ),
% 43.27/6.00      inference(demodulation,[status(thm)],[c_65250,c_7561]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_5953,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0))) = k5_xboole_0(X0,k4_xboole_0(X0,X0)) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_1,c_5942]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_5968,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0))) = X0 ),
% 43.27/6.00      inference(light_normalisation,[status(thm)],[c_5953,c_1]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_6166,plain,
% 43.27/6.00      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X0)),k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X0),X0))),k4_xboole_0(X0,X0)) = k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)),X0))) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_5968,c_3]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_6199,plain,
% 43.27/6.00      ( k4_xboole_0(k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,k4_xboole_0(X0,X0))),X0),k4_xboole_0(X0,X0)) = k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)),X0))) ),
% 43.27/6.00      inference(demodulation,[status(thm)],[c_6166,c_3]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_6171,plain,
% 43.27/6.00      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),X0) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_48,c_3]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_6200,plain,
% 43.27/6.00      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X0)),k5_xboole_0(X0,k4_xboole_0(X0,X0))),k4_xboole_0(X0,X0)) = k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)),X0))) ),
% 43.27/6.00      inference(demodulation,[status(thm)],[c_6199,c_6171]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_6202,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)),X0))) = k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(X0,X0)) ),
% 43.27/6.00      inference(light_normalisation,[status(thm)],[c_6200,c_1]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_6599,plain,
% 43.27/6.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_6269,c_6214]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_23816,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)),X0))) = k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(X0,X0)) ),
% 43.27/6.00      inference(demodulation,[status(thm)],[c_6202,c_6599]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_6369,plain,
% 43.27/6.00      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,X1),X0)),X1) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_6339,c_2]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_24185,plain,
% 43.27/6.00      ( k5_xboole_0(k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0))),X0),k5_xboole_0(k4_xboole_0(k5_xboole_0(X0,X0),X0),k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k5_xboole_0(X0,X0),X0)),k4_xboole_0(k5_xboole_0(X0,X0),X0)))) = k4_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,X0),X0),X0))) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_6369,c_4]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_7002,plain,
% 43.27/6.00      ( k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0))) = k4_xboole_0(k5_xboole_0(X0,X0),X0) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_6339,c_6597]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_7028,plain,
% 43.27/6.00      ( k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0))) = k5_xboole_0(X0,X0) ),
% 43.27/6.00      inference(light_normalisation,[status(thm)],[c_7002,c_6339]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_7602,plain,
% 43.27/6.00      ( k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X0)))) = k5_xboole_0(X0,X0) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_8,c_7028]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_7298,plain,
% 43.27/6.00      ( k5_xboole_0(k4_xboole_0(k5_xboole_0(X0,X0),X0),k4_xboole_0(k5_xboole_0(X0,X0),X0)) = k4_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0)) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_6339,c_6599]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_7374,plain,
% 43.27/6.00      ( k4_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0)) = k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0)) ),
% 43.27/6.00      inference(light_normalisation,[status(thm)],[c_7298,c_6339]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_8648,plain,
% 43.27/6.00      ( k4_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0)) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X0))) ),
% 43.27/6.00      inference(demodulation,[status(thm)],[c_7561,c_7374]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_10527,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,X0)))) = k5_xboole_0(k5_xboole_0(X0,X0),X0) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_1,c_6102]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_10725,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k5_xboole_0(X0,X0)) = k5_xboole_0(k5_xboole_0(X0,X0),X0) ),
% 43.27/6.00      inference(light_normalisation,[status(thm)],[c_10527,c_1]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_6359,plain,
% 43.27/6.00      ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_8,c_6339]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_13084,plain,
% 43.27/6.00      ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))),k5_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) ),
% 43.27/6.00      inference(demodulation,[status(thm)],[c_6359,c_7561]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_13163,plain,
% 43.27/6.00      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X0)))),k5_xboole_0(X0,k5_xboole_0(X0,X0))) = k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X0),X0))) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_10725,c_13084]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_13290,plain,
% 43.27/6.00      ( k4_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,k5_xboole_0(X0,X0))) = k5_xboole_0(X0,X0) ),
% 43.27/6.00      inference(light_normalisation,
% 43.27/6.00                [status(thm)],
% 43.27/6.00                [c_13163,c_7602,c_10725]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_24261,plain,
% 43.27/6.00      ( k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X0))),k5_xboole_0(X0,X0)))) = k5_xboole_0(X0,X0) ),
% 43.27/6.00      inference(light_normalisation,
% 43.27/6.00                [status(thm)],
% 43.27/6.00                [c_24185,c_6339,c_7602,c_8648,c_13290]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_17354,plain,
% 43.27/6.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X0))),k5_xboole_0(X0,X0)) = k5_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(X0,X0)) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_8026,c_7744]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_17356,plain,
% 43.27/6.00      ( k5_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = k5_xboole_0(X0,X0) ),
% 43.27/6.00      inference(light_normalisation,[status(thm)],[c_17354,c_7406]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_17334,plain,
% 43.27/6.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X0))),k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),X1),X2) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_8026,c_8527]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_17407,plain,
% 43.27/6.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),X1),X2) = k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X1,X2)) ),
% 43.27/6.00      inference(demodulation,[status(thm)],[c_17334,c_8026]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_17409,plain,
% 43.27/6.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),X1),X2) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) ),
% 43.27/6.00      inference(demodulation,[status(thm)],[c_17407,c_7561]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_18001,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X0),X1))) = k5_xboole_0(k5_xboole_0(X0,X0),X1) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_17356,c_17409]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_18537,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X0),X1) ),
% 43.27/6.00      inference(light_normalisation,[status(thm)],[c_18001,c_5942]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_24262,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X0))),k5_xboole_0(X0,X0)))))) = k5_xboole_0(X0,X0) ),
% 43.27/6.00      inference(demodulation,[status(thm)],[c_24261,c_18537]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_8353,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X0))))) = k5_xboole_0(X0,X0) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_7602,c_8]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_24263,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X0))) = k5_xboole_0(X0,X0) ),
% 43.27/6.00      inference(demodulation,[status(thm)],[c_24262,c_8353,c_13084]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_18565,plain,
% 43.27/6.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,X1)),X2) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) ),
% 43.27/6.00      inference(demodulation,[status(thm)],[c_18537,c_17409]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_25279,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X0),X1))) = k5_xboole_0(k5_xboole_0(X0,X0),X1) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_24263,c_18565]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_25314,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X1)))) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
% 43.27/6.00      inference(light_normalisation,[status(thm)],[c_25279,c_18537]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_26067,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)),X0))) = k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(X0,X0)))) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_23816,c_25314]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_6130,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X0))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0)) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_2,c_5942]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_11768,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,X0),X0),k4_xboole_0(X0,X0))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,X0)),X0)) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_6339,c_6130]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_11871,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(X0,X0))) = k5_xboole_0(X0,k5_xboole_0(X0,X0)) ),
% 43.27/6.00      inference(light_normalisation,
% 43.27/6.00                [status(thm)],
% 43.27/6.00                [c_11768,c_6320,c_6339]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_26535,plain,
% 43.27/6.00      ( k4_xboole_0(k5_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = k5_xboole_0(X0,X0) ),
% 43.27/6.00      inference(light_normalisation,
% 43.27/6.00                [status(thm)],
% 43.27/6.00                [c_26067,c_11871,c_23816,c_24263]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_26667,plain,
% 43.27/6.00      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,X0),X0)),X0) = k5_xboole_0(k4_xboole_0(X0,X0),k5_xboole_0(X0,X0)) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_26535,c_6369]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_26669,plain,
% 43.27/6.00      ( k5_xboole_0(k4_xboole_0(X0,X0),k5_xboole_0(X0,X0)) = k5_xboole_0(X0,X0) ),
% 43.27/6.00      inference(light_normalisation,
% 43.27/6.00                [status(thm)],
% 43.27/6.00                [c_26667,c_6320,c_6339]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_26835,plain,
% 43.27/6.00      ( k5_xboole_0(k4_xboole_0(X0,X0),k5_xboole_0(X0,k5_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,X0),X1) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_26669,c_8527]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_26877,plain,
% 43.27/6.00      ( k5_xboole_0(k4_xboole_0(X0,X0),k5_xboole_0(X0,k5_xboole_0(X0,X1))) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
% 43.27/6.00      inference(light_normalisation,[status(thm)],[c_26835,c_18537]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_6321,plain,
% 43.27/6.00      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))),k5_xboole_0(X0,X1)),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_8,c_6214]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_8125,plain,
% 43.27/6.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),X4) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),X3),X4)) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_7501,c_8]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_8214,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X4)))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),X4) ),
% 43.27/6.00      inference(demodulation,[status(thm)],[c_8125,c_7501]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_33712,plain,
% 43.27/6.00      ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))))),k5_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) ),
% 43.27/6.00      inference(demodulation,[status(thm)],[c_6321,c_7561,c_8214]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_33776,plain,
% 43.27/6.00      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X0),k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X0),k5_xboole_0(X0,X0)))),k5_xboole_0(k4_xboole_0(X0,X0),X0)) = k5_xboole_0(k4_xboole_0(X0,X0),k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X0),X0))) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_5942,c_33712]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_34438,plain,
% 43.27/6.00      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X0),k5_xboole_0(X0,k5_xboole_0(X0,X0))),k5_xboole_0(k4_xboole_0(X0,X0),X0)) = k5_xboole_0(k4_xboole_0(X0,X0),k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X0),X0))) ),
% 43.27/6.00      inference(light_normalisation,[status(thm)],[c_33776,c_26669]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_34439,plain,
% 43.27/6.00      ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,X0)),k5_xboole_0(k4_xboole_0(X0,X0),X0)) = k5_xboole_0(X0,X0) ),
% 43.27/6.00      inference(demodulation,
% 43.27/6.00                [status(thm)],
% 43.27/6.00                [c_34438,c_5942,c_26669,c_26877]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_65253,plain,
% 43.27/6.00      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X0),X0),X0) = k5_xboole_0(X0,X0) ),
% 43.27/6.00      inference(demodulation,
% 43.27/6.00                [status(thm)],
% 43.27/6.00                [c_65252,c_5965,c_26877,c_34439]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_67306,plain,
% 43.27/6.00      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X0),X0),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X0),X1) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_65253,c_8]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_67474,plain,
% 43.27/6.00      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X0),X0),k5_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
% 43.27/6.00      inference(light_normalisation,[status(thm)],[c_67306,c_18537]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_91682,plain,
% 43.27/6.00      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)),k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)))))),X1) = k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)))))) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_91392,c_67474]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_91684,plain,
% 43.27/6.00      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))))),X1) = k4_xboole_0(X0,X1) ),
% 43.27/6.00      inference(light_normalisation,
% 43.27/6.00                [status(thm)],
% 43.27/6.00                [c_91682,c_6269,c_6597,c_6599]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_91935,plain,
% 43.27/6.00      ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,X0)))),X1),X1) = k4_xboole_0(X0,X1) ),
% 43.27/6.00      inference(demodulation,[status(thm)],[c_91613,c_91684]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_91938,plain,
% 43.27/6.00      ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,X0)),X1),X1) = k4_xboole_0(X0,X1) ),
% 43.27/6.00      inference(light_normalisation,[status(thm)],[c_91935,c_1]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_92598,plain,
% 43.27/6.00      ( k4_xboole_0(k5_xboole_0(X0,X0),X0) = k4_xboole_0(X0,X0) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_6320,c_91938]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_93047,plain,
% 43.27/6.00      ( k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
% 43.27/6.00      inference(light_normalisation,[status(thm)],[c_92598,c_6339]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_94061,plain,
% 43.27/6.00      ( k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
% 43.27/6.00      inference(demodulation,[status(thm)],[c_93047,c_1]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_123699,plain,
% 43.27/6.00      ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 43.27/6.00      inference(light_normalisation,
% 43.27/6.00                [status(thm)],
% 43.27/6.00                [c_123698,c_93047,c_94061]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_127195,plain,
% 43.27/6.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
% 43.27/6.00      inference(superposition,[status(thm)],[c_48,c_123699]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_127759,plain,
% 43.27/6.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 43.27/6.00      inference(light_normalisation,[status(thm)],[c_127195,c_123699]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_129757,plain,
% 43.27/6.00      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X1),X0)) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1) ),
% 43.27/6.00      inference(demodulation,[status(thm)],[c_127759,c_2]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_10,negated_conjecture,
% 43.27/6.00      ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))) ),
% 43.27/6.00      inference(cnf_transformation,[],[f46]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_5940,plain,
% 43.27/6.00      ( k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k4_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))) ),
% 43.27/6.00      inference(demodulation,[status(thm)],[c_8,c_10]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_127148,plain,
% 43.27/6.00      ( k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1)))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))) ),
% 43.27/6.00      inference(demodulation,[status(thm)],[c_123699,c_5940]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_131447,plain,
% 43.27/6.00      ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))) ),
% 43.27/6.00      inference(demodulation,[status(thm)],[c_129757,c_127148]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_59,plain,( X0 = X0 ),theory(equality) ).
% 43.27/6.00  
% 43.27/6.00  cnf(c_7593,plain,
% 43.27/6.00      ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))) = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))) ),
% 43.27/6.00      inference(instantiation,[status(thm)],[c_59]) ).
% 43.27/6.00  
% 43.27/6.00  cnf(contradiction,plain,
% 43.27/6.00      ( $false ),
% 43.27/6.00      inference(minisat,[status(thm)],[c_131447,c_7593]) ).
% 43.27/6.00  
% 43.27/6.00  
% 43.27/6.00  % SZS output end CNFRefutation for theBenchmark.p
% 43.27/6.00  
% 43.27/6.00  ------                               Statistics
% 43.27/6.00  
% 43.27/6.00  ------ Selected
% 43.27/6.00  
% 43.27/6.00  total_time:                             5.095
% 43.27/6.00  
%------------------------------------------------------------------------------
