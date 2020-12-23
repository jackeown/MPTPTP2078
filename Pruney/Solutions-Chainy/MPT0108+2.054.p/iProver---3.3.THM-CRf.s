%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:35 EST 2020

% Result     : Theorem 7.29s
% Output     : CNFRefutation 7.29s
% Verified   : 
% Statistics : Number of formulae       :   79 (1101 expanded)
%              Number of clauses        :   51 ( 391 expanded)
%              Number of leaves         :   11 ( 315 expanded)
%              Depth                    :   18
%              Number of atoms          :   80 (1102 expanded)
%              Number of equality atoms :   79 (1101 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f23,f16])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f18,f25])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f10,conjecture,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1) ),
    inference(negated_conjecture,[],[f10])).

fof(f12,plain,(
    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k5_xboole_0(X0,X1) ),
    inference(ennf_transformation,[],[f11])).

fof(f13,plain,
    ( ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k5_xboole_0(X0,X1)
   => k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).

fof(f24,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f28,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f24,f16,f25])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f19,f16,f16])).

cnf(c_5,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_38,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_6])).

cnf(c_36,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_6,c_5])).

cnf(c_79,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6,c_36])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_94,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_79,c_4])).

cnf(c_95,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_94,c_36])).

cnf(c_143,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_38,c_95])).

cnf(c_151,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_143,c_4])).

cnf(c_163,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_151,c_95])).

cnf(c_168,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_5,c_163])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_2,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_1,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_21,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_2,c_1,c_0])).

cnf(c_255,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_21])).

cnf(c_3290,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_168,c_255])).

cnf(c_7,negated_conjecture,
    ( k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_19,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))) != k5_xboole_0(sK0,sK1) ),
    inference(theory_normalisation,[status(thm)],[c_7,c_1,c_0])).

cnf(c_32,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))) != k5_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_5,c_19])).

cnf(c_24105,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))) != k5_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_3290,c_32])).

cnf(c_254,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(superposition,[status(thm)],[c_94,c_21])).

cnf(c_3,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_20,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(theory_normalisation,[status(thm)],[c_3,c_1,c_0])).

cnf(c_262,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_21,c_20])).

cnf(c_265,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X1,X1)) ),
    inference(demodulation,[status(thm)],[c_262,c_21])).

cnf(c_266,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_265,c_6])).

cnf(c_269,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(demodulation,[status(thm)],[c_254,c_266])).

cnf(c_270,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_269,c_4])).

cnf(c_30,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X2,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_360,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_270,c_30])).

cnf(c_516,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),X0) = k3_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_21,c_360])).

cnf(c_565,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_516,c_270])).

cnf(c_51,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),X3)) = k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X3) ),
    inference(superposition,[status(thm)],[c_20,c_5])).

cnf(c_7182,plain,
    ( k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k3_xboole_0(X0,X2))),X3) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X2)),X3)) ),
    inference(superposition,[status(thm)],[c_565,c_51])).

cnf(c_42,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,k3_xboole_0(X0,X2))) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_0,c_20])).

cnf(c_843,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X2))) = k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_21,c_42])).

cnf(c_358,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X2)) = k3_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_21,c_30])).

cnf(c_934,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k3_xboole_0(X0,X2))) = k5_xboole_0(X0,k3_xboole_0(X2,X0)) ),
    inference(light_normalisation,[status(thm)],[c_843,c_358])).

cnf(c_5667,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_565,c_1])).

cnf(c_7540,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),X2)) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X2) ),
    inference(light_normalisation,[status(thm)],[c_7182,c_934,c_5667])).

cnf(c_24106,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK0),k3_xboole_0(sK0,sK1)))) != k5_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_24105,c_7540])).

cnf(c_885,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X0))) ),
    inference(superposition,[status(thm)],[c_270,c_42])).

cnf(c_29,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_320,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_270,c_29])).

cnf(c_439,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_320,c_20])).

cnf(c_914,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_885,c_6,c_270,c_439])).

cnf(c_915,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_914,c_266,c_439])).

cnf(c_24107,plain,
    ( k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_24106,c_4,c_915])).

cnf(c_24108,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_24107])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:53:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.29/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.29/1.51  
% 7.29/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.29/1.51  
% 7.29/1.51  ------  iProver source info
% 7.29/1.51  
% 7.29/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.29/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.29/1.51  git: non_committed_changes: false
% 7.29/1.51  git: last_make_outside_of_git: false
% 7.29/1.51  
% 7.29/1.51  ------ 
% 7.29/1.51  
% 7.29/1.51  ------ Input Options
% 7.29/1.51  
% 7.29/1.51  --out_options                           all
% 7.29/1.51  --tptp_safe_out                         true
% 7.29/1.51  --problem_path                          ""
% 7.29/1.51  --include_path                          ""
% 7.29/1.51  --clausifier                            res/vclausify_rel
% 7.29/1.51  --clausifier_options                    --mode clausify
% 7.29/1.51  --stdin                                 false
% 7.29/1.51  --stats_out                             all
% 7.29/1.51  
% 7.29/1.51  ------ General Options
% 7.29/1.51  
% 7.29/1.51  --fof                                   false
% 7.29/1.51  --time_out_real                         305.
% 7.29/1.51  --time_out_virtual                      -1.
% 7.29/1.51  --symbol_type_check                     false
% 7.29/1.51  --clausify_out                          false
% 7.29/1.51  --sig_cnt_out                           false
% 7.29/1.51  --trig_cnt_out                          false
% 7.29/1.51  --trig_cnt_out_tolerance                1.
% 7.29/1.51  --trig_cnt_out_sk_spl                   false
% 7.29/1.51  --abstr_cl_out                          false
% 7.29/1.51  
% 7.29/1.51  ------ Global Options
% 7.29/1.51  
% 7.29/1.51  --schedule                              default
% 7.29/1.51  --add_important_lit                     false
% 7.29/1.51  --prop_solver_per_cl                    1000
% 7.29/1.51  --min_unsat_core                        false
% 7.29/1.51  --soft_assumptions                      false
% 7.29/1.51  --soft_lemma_size                       3
% 7.29/1.51  --prop_impl_unit_size                   0
% 7.29/1.51  --prop_impl_unit                        []
% 7.29/1.51  --share_sel_clauses                     true
% 7.29/1.51  --reset_solvers                         false
% 7.29/1.51  --bc_imp_inh                            [conj_cone]
% 7.29/1.51  --conj_cone_tolerance                   3.
% 7.29/1.51  --extra_neg_conj                        none
% 7.29/1.51  --large_theory_mode                     true
% 7.29/1.51  --prolific_symb_bound                   200
% 7.29/1.51  --lt_threshold                          2000
% 7.29/1.51  --clause_weak_htbl                      true
% 7.29/1.51  --gc_record_bc_elim                     false
% 7.29/1.51  
% 7.29/1.51  ------ Preprocessing Options
% 7.29/1.51  
% 7.29/1.51  --preprocessing_flag                    true
% 7.29/1.51  --time_out_prep_mult                    0.1
% 7.29/1.51  --splitting_mode                        input
% 7.29/1.51  --splitting_grd                         true
% 7.29/1.51  --splitting_cvd                         false
% 7.29/1.51  --splitting_cvd_svl                     false
% 7.29/1.51  --splitting_nvd                         32
% 7.29/1.51  --sub_typing                            true
% 7.29/1.51  --prep_gs_sim                           true
% 7.29/1.51  --prep_unflatten                        true
% 7.29/1.51  --prep_res_sim                          true
% 7.29/1.51  --prep_upred                            true
% 7.29/1.51  --prep_sem_filter                       exhaustive
% 7.29/1.51  --prep_sem_filter_out                   false
% 7.29/1.51  --pred_elim                             true
% 7.29/1.51  --res_sim_input                         true
% 7.29/1.51  --eq_ax_congr_red                       true
% 7.29/1.51  --pure_diseq_elim                       true
% 7.29/1.51  --brand_transform                       false
% 7.29/1.51  --non_eq_to_eq                          false
% 7.29/1.51  --prep_def_merge                        true
% 7.29/1.51  --prep_def_merge_prop_impl              false
% 7.29/1.51  --prep_def_merge_mbd                    true
% 7.29/1.51  --prep_def_merge_tr_red                 false
% 7.29/1.51  --prep_def_merge_tr_cl                  false
% 7.29/1.51  --smt_preprocessing                     true
% 7.29/1.51  --smt_ac_axioms                         fast
% 7.29/1.51  --preprocessed_out                      false
% 7.29/1.51  --preprocessed_stats                    false
% 7.29/1.51  
% 7.29/1.51  ------ Abstraction refinement Options
% 7.29/1.51  
% 7.29/1.51  --abstr_ref                             []
% 7.29/1.51  --abstr_ref_prep                        false
% 7.29/1.51  --abstr_ref_until_sat                   false
% 7.29/1.51  --abstr_ref_sig_restrict                funpre
% 7.29/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.29/1.51  --abstr_ref_under                       []
% 7.29/1.51  
% 7.29/1.51  ------ SAT Options
% 7.29/1.51  
% 7.29/1.51  --sat_mode                              false
% 7.29/1.51  --sat_fm_restart_options                ""
% 7.29/1.51  --sat_gr_def                            false
% 7.29/1.51  --sat_epr_types                         true
% 7.29/1.51  --sat_non_cyclic_types                  false
% 7.29/1.51  --sat_finite_models                     false
% 7.29/1.51  --sat_fm_lemmas                         false
% 7.29/1.51  --sat_fm_prep                           false
% 7.29/1.51  --sat_fm_uc_incr                        true
% 7.29/1.51  --sat_out_model                         small
% 7.29/1.51  --sat_out_clauses                       false
% 7.29/1.51  
% 7.29/1.51  ------ QBF Options
% 7.29/1.51  
% 7.29/1.51  --qbf_mode                              false
% 7.29/1.51  --qbf_elim_univ                         false
% 7.29/1.51  --qbf_dom_inst                          none
% 7.29/1.51  --qbf_dom_pre_inst                      false
% 7.29/1.51  --qbf_sk_in                             false
% 7.29/1.51  --qbf_pred_elim                         true
% 7.29/1.51  --qbf_split                             512
% 7.29/1.51  
% 7.29/1.51  ------ BMC1 Options
% 7.29/1.51  
% 7.29/1.51  --bmc1_incremental                      false
% 7.29/1.51  --bmc1_axioms                           reachable_all
% 7.29/1.51  --bmc1_min_bound                        0
% 7.29/1.51  --bmc1_max_bound                        -1
% 7.29/1.51  --bmc1_max_bound_default                -1
% 7.29/1.51  --bmc1_symbol_reachability              true
% 7.29/1.51  --bmc1_property_lemmas                  false
% 7.29/1.51  --bmc1_k_induction                      false
% 7.29/1.51  --bmc1_non_equiv_states                 false
% 7.29/1.51  --bmc1_deadlock                         false
% 7.29/1.51  --bmc1_ucm                              false
% 7.29/1.51  --bmc1_add_unsat_core                   none
% 7.29/1.51  --bmc1_unsat_core_children              false
% 7.29/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.29/1.51  --bmc1_out_stat                         full
% 7.29/1.51  --bmc1_ground_init                      false
% 7.29/1.51  --bmc1_pre_inst_next_state              false
% 7.29/1.51  --bmc1_pre_inst_state                   false
% 7.29/1.51  --bmc1_pre_inst_reach_state             false
% 7.29/1.51  --bmc1_out_unsat_core                   false
% 7.29/1.51  --bmc1_aig_witness_out                  false
% 7.29/1.51  --bmc1_verbose                          false
% 7.29/1.51  --bmc1_dump_clauses_tptp                false
% 7.29/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.29/1.51  --bmc1_dump_file                        -
% 7.29/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.29/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.29/1.51  --bmc1_ucm_extend_mode                  1
% 7.29/1.51  --bmc1_ucm_init_mode                    2
% 7.29/1.51  --bmc1_ucm_cone_mode                    none
% 7.29/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.29/1.51  --bmc1_ucm_relax_model                  4
% 7.29/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.29/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.29/1.51  --bmc1_ucm_layered_model                none
% 7.29/1.51  --bmc1_ucm_max_lemma_size               10
% 7.29/1.51  
% 7.29/1.51  ------ AIG Options
% 7.29/1.51  
% 7.29/1.51  --aig_mode                              false
% 7.29/1.51  
% 7.29/1.51  ------ Instantiation Options
% 7.29/1.51  
% 7.29/1.51  --instantiation_flag                    true
% 7.29/1.51  --inst_sos_flag                         false
% 7.29/1.51  --inst_sos_phase                        true
% 7.29/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.29/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.29/1.51  --inst_lit_sel_side                     num_symb
% 7.29/1.51  --inst_solver_per_active                1400
% 7.29/1.51  --inst_solver_calls_frac                1.
% 7.29/1.51  --inst_passive_queue_type               priority_queues
% 7.29/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.29/1.51  --inst_passive_queues_freq              [25;2]
% 7.29/1.51  --inst_dismatching                      true
% 7.29/1.51  --inst_eager_unprocessed_to_passive     true
% 7.29/1.51  --inst_prop_sim_given                   true
% 7.29/1.51  --inst_prop_sim_new                     false
% 7.29/1.51  --inst_subs_new                         false
% 7.29/1.51  --inst_eq_res_simp                      false
% 7.29/1.51  --inst_subs_given                       false
% 7.29/1.51  --inst_orphan_elimination               true
% 7.29/1.51  --inst_learning_loop_flag               true
% 7.29/1.51  --inst_learning_start                   3000
% 7.29/1.51  --inst_learning_factor                  2
% 7.29/1.51  --inst_start_prop_sim_after_learn       3
% 7.29/1.51  --inst_sel_renew                        solver
% 7.29/1.51  --inst_lit_activity_flag                true
% 7.29/1.51  --inst_restr_to_given                   false
% 7.29/1.51  --inst_activity_threshold               500
% 7.29/1.51  --inst_out_proof                        true
% 7.29/1.51  
% 7.29/1.51  ------ Resolution Options
% 7.29/1.51  
% 7.29/1.51  --resolution_flag                       true
% 7.29/1.51  --res_lit_sel                           adaptive
% 7.29/1.51  --res_lit_sel_side                      none
% 7.29/1.51  --res_ordering                          kbo
% 7.29/1.51  --res_to_prop_solver                    active
% 7.29/1.51  --res_prop_simpl_new                    false
% 7.29/1.51  --res_prop_simpl_given                  true
% 7.29/1.51  --res_passive_queue_type                priority_queues
% 7.29/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.29/1.51  --res_passive_queues_freq               [15;5]
% 7.29/1.51  --res_forward_subs                      full
% 7.29/1.51  --res_backward_subs                     full
% 7.29/1.51  --res_forward_subs_resolution           true
% 7.29/1.51  --res_backward_subs_resolution          true
% 7.29/1.51  --res_orphan_elimination                true
% 7.29/1.51  --res_time_limit                        2.
% 7.29/1.51  --res_out_proof                         true
% 7.29/1.51  
% 7.29/1.51  ------ Superposition Options
% 7.29/1.51  
% 7.29/1.51  --superposition_flag                    true
% 7.29/1.51  --sup_passive_queue_type                priority_queues
% 7.29/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.29/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.29/1.51  --demod_completeness_check              fast
% 7.29/1.51  --demod_use_ground                      true
% 7.29/1.51  --sup_to_prop_solver                    passive
% 7.29/1.51  --sup_prop_simpl_new                    true
% 7.29/1.51  --sup_prop_simpl_given                  true
% 7.29/1.51  --sup_fun_splitting                     false
% 7.29/1.51  --sup_smt_interval                      50000
% 7.29/1.51  
% 7.29/1.51  ------ Superposition Simplification Setup
% 7.29/1.51  
% 7.29/1.51  --sup_indices_passive                   []
% 7.29/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.29/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.29/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.29/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.29/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.29/1.51  --sup_full_bw                           [BwDemod]
% 7.29/1.51  --sup_immed_triv                        [TrivRules]
% 7.29/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.29/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.29/1.51  --sup_immed_bw_main                     []
% 7.29/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.29/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.29/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.29/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.29/1.51  
% 7.29/1.51  ------ Combination Options
% 7.29/1.51  
% 7.29/1.51  --comb_res_mult                         3
% 7.29/1.51  --comb_sup_mult                         2
% 7.29/1.51  --comb_inst_mult                        10
% 7.29/1.51  
% 7.29/1.51  ------ Debug Options
% 7.29/1.51  
% 7.29/1.51  --dbg_backtrace                         false
% 7.29/1.51  --dbg_dump_prop_clauses                 false
% 7.29/1.51  --dbg_dump_prop_clauses_file            -
% 7.29/1.51  --dbg_out_stat                          false
% 7.29/1.51  ------ Parsing...
% 7.29/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.29/1.51  
% 7.29/1.51  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 7.29/1.51  
% 7.29/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.29/1.51  
% 7.29/1.51  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.29/1.51  ------ Proving...
% 7.29/1.51  ------ Problem Properties 
% 7.29/1.51  
% 7.29/1.51  
% 7.29/1.51  clauses                                 8
% 7.29/1.51  conjectures                             1
% 7.29/1.51  EPR                                     0
% 7.29/1.51  Horn                                    8
% 7.29/1.51  unary                                   8
% 7.29/1.51  binary                                  0
% 7.29/1.51  lits                                    8
% 7.29/1.51  lits eq                                 8
% 7.29/1.51  fd_pure                                 0
% 7.29/1.51  fd_pseudo                               0
% 7.29/1.51  fd_cond                                 0
% 7.29/1.51  fd_pseudo_cond                          0
% 7.29/1.51  AC symbols                              1
% 7.29/1.51  
% 7.29/1.51  ------ Schedule UEQ
% 7.29/1.51  
% 7.29/1.51  ------ pure equality problem: resolution off 
% 7.29/1.51  
% 7.29/1.51  ------ Option_UEQ Time Limit: Unbounded
% 7.29/1.51  
% 7.29/1.51  
% 7.29/1.51  ------ 
% 7.29/1.51  Current options:
% 7.29/1.51  ------ 
% 7.29/1.51  
% 7.29/1.51  ------ Input Options
% 7.29/1.51  
% 7.29/1.51  --out_options                           all
% 7.29/1.51  --tptp_safe_out                         true
% 7.29/1.51  --problem_path                          ""
% 7.29/1.51  --include_path                          ""
% 7.29/1.51  --clausifier                            res/vclausify_rel
% 7.29/1.51  --clausifier_options                    --mode clausify
% 7.29/1.51  --stdin                                 false
% 7.29/1.51  --stats_out                             all
% 7.29/1.51  
% 7.29/1.51  ------ General Options
% 7.29/1.51  
% 7.29/1.51  --fof                                   false
% 7.29/1.51  --time_out_real                         305.
% 7.29/1.51  --time_out_virtual                      -1.
% 7.29/1.51  --symbol_type_check                     false
% 7.29/1.51  --clausify_out                          false
% 7.29/1.51  --sig_cnt_out                           false
% 7.29/1.51  --trig_cnt_out                          false
% 7.29/1.51  --trig_cnt_out_tolerance                1.
% 7.29/1.51  --trig_cnt_out_sk_spl                   false
% 7.29/1.51  --abstr_cl_out                          false
% 7.29/1.51  
% 7.29/1.51  ------ Global Options
% 7.29/1.51  
% 7.29/1.51  --schedule                              default
% 7.29/1.51  --add_important_lit                     false
% 7.29/1.51  --prop_solver_per_cl                    1000
% 7.29/1.51  --min_unsat_core                        false
% 7.29/1.51  --soft_assumptions                      false
% 7.29/1.51  --soft_lemma_size                       3
% 7.29/1.51  --prop_impl_unit_size                   0
% 7.29/1.51  --prop_impl_unit                        []
% 7.29/1.51  --share_sel_clauses                     true
% 7.29/1.51  --reset_solvers                         false
% 7.29/1.51  --bc_imp_inh                            [conj_cone]
% 7.29/1.51  --conj_cone_tolerance                   3.
% 7.29/1.51  --extra_neg_conj                        none
% 7.29/1.51  --large_theory_mode                     true
% 7.29/1.51  --prolific_symb_bound                   200
% 7.29/1.51  --lt_threshold                          2000
% 7.29/1.51  --clause_weak_htbl                      true
% 7.29/1.51  --gc_record_bc_elim                     false
% 7.29/1.51  
% 7.29/1.51  ------ Preprocessing Options
% 7.29/1.51  
% 7.29/1.51  --preprocessing_flag                    true
% 7.29/1.51  --time_out_prep_mult                    0.1
% 7.29/1.51  --splitting_mode                        input
% 7.29/1.51  --splitting_grd                         true
% 7.29/1.51  --splitting_cvd                         false
% 7.29/1.51  --splitting_cvd_svl                     false
% 7.29/1.51  --splitting_nvd                         32
% 7.29/1.51  --sub_typing                            true
% 7.29/1.51  --prep_gs_sim                           true
% 7.29/1.51  --prep_unflatten                        true
% 7.29/1.51  --prep_res_sim                          true
% 7.29/1.51  --prep_upred                            true
% 7.29/1.51  --prep_sem_filter                       exhaustive
% 7.29/1.51  --prep_sem_filter_out                   false
% 7.29/1.51  --pred_elim                             true
% 7.29/1.51  --res_sim_input                         true
% 7.29/1.51  --eq_ax_congr_red                       true
% 7.29/1.51  --pure_diseq_elim                       true
% 7.29/1.51  --brand_transform                       false
% 7.29/1.51  --non_eq_to_eq                          false
% 7.29/1.51  --prep_def_merge                        true
% 7.29/1.51  --prep_def_merge_prop_impl              false
% 7.29/1.51  --prep_def_merge_mbd                    true
% 7.29/1.51  --prep_def_merge_tr_red                 false
% 7.29/1.51  --prep_def_merge_tr_cl                  false
% 7.29/1.51  --smt_preprocessing                     true
% 7.29/1.51  --smt_ac_axioms                         fast
% 7.29/1.51  --preprocessed_out                      false
% 7.29/1.51  --preprocessed_stats                    false
% 7.29/1.51  
% 7.29/1.51  ------ Abstraction refinement Options
% 7.29/1.51  
% 7.29/1.51  --abstr_ref                             []
% 7.29/1.51  --abstr_ref_prep                        false
% 7.29/1.51  --abstr_ref_until_sat                   false
% 7.29/1.51  --abstr_ref_sig_restrict                funpre
% 7.29/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.29/1.51  --abstr_ref_under                       []
% 7.29/1.51  
% 7.29/1.51  ------ SAT Options
% 7.29/1.51  
% 7.29/1.51  --sat_mode                              false
% 7.29/1.51  --sat_fm_restart_options                ""
% 7.29/1.51  --sat_gr_def                            false
% 7.29/1.51  --sat_epr_types                         true
% 7.29/1.51  --sat_non_cyclic_types                  false
% 7.29/1.51  --sat_finite_models                     false
% 7.29/1.51  --sat_fm_lemmas                         false
% 7.29/1.51  --sat_fm_prep                           false
% 7.29/1.51  --sat_fm_uc_incr                        true
% 7.29/1.51  --sat_out_model                         small
% 7.29/1.51  --sat_out_clauses                       false
% 7.29/1.51  
% 7.29/1.51  ------ QBF Options
% 7.29/1.51  
% 7.29/1.51  --qbf_mode                              false
% 7.29/1.51  --qbf_elim_univ                         false
% 7.29/1.51  --qbf_dom_inst                          none
% 7.29/1.51  --qbf_dom_pre_inst                      false
% 7.29/1.51  --qbf_sk_in                             false
% 7.29/1.51  --qbf_pred_elim                         true
% 7.29/1.51  --qbf_split                             512
% 7.29/1.51  
% 7.29/1.51  ------ BMC1 Options
% 7.29/1.51  
% 7.29/1.51  --bmc1_incremental                      false
% 7.29/1.51  --bmc1_axioms                           reachable_all
% 7.29/1.51  --bmc1_min_bound                        0
% 7.29/1.51  --bmc1_max_bound                        -1
% 7.29/1.51  --bmc1_max_bound_default                -1
% 7.29/1.51  --bmc1_symbol_reachability              true
% 7.29/1.51  --bmc1_property_lemmas                  false
% 7.29/1.51  --bmc1_k_induction                      false
% 7.29/1.51  --bmc1_non_equiv_states                 false
% 7.29/1.51  --bmc1_deadlock                         false
% 7.29/1.51  --bmc1_ucm                              false
% 7.29/1.51  --bmc1_add_unsat_core                   none
% 7.29/1.51  --bmc1_unsat_core_children              false
% 7.29/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.29/1.51  --bmc1_out_stat                         full
% 7.29/1.51  --bmc1_ground_init                      false
% 7.29/1.51  --bmc1_pre_inst_next_state              false
% 7.29/1.51  --bmc1_pre_inst_state                   false
% 7.29/1.51  --bmc1_pre_inst_reach_state             false
% 7.29/1.51  --bmc1_out_unsat_core                   false
% 7.29/1.51  --bmc1_aig_witness_out                  false
% 7.29/1.51  --bmc1_verbose                          false
% 7.29/1.51  --bmc1_dump_clauses_tptp                false
% 7.29/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.29/1.51  --bmc1_dump_file                        -
% 7.29/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.29/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.29/1.51  --bmc1_ucm_extend_mode                  1
% 7.29/1.51  --bmc1_ucm_init_mode                    2
% 7.29/1.51  --bmc1_ucm_cone_mode                    none
% 7.29/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.29/1.51  --bmc1_ucm_relax_model                  4
% 7.29/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.29/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.29/1.51  --bmc1_ucm_layered_model                none
% 7.29/1.51  --bmc1_ucm_max_lemma_size               10
% 7.29/1.51  
% 7.29/1.51  ------ AIG Options
% 7.29/1.51  
% 7.29/1.51  --aig_mode                              false
% 7.29/1.51  
% 7.29/1.51  ------ Instantiation Options
% 7.29/1.51  
% 7.29/1.51  --instantiation_flag                    false
% 7.29/1.51  --inst_sos_flag                         false
% 7.29/1.51  --inst_sos_phase                        true
% 7.29/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.29/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.29/1.51  --inst_lit_sel_side                     num_symb
% 7.29/1.51  --inst_solver_per_active                1400
% 7.29/1.51  --inst_solver_calls_frac                1.
% 7.29/1.51  --inst_passive_queue_type               priority_queues
% 7.29/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.29/1.51  --inst_passive_queues_freq              [25;2]
% 7.29/1.51  --inst_dismatching                      true
% 7.29/1.51  --inst_eager_unprocessed_to_passive     true
% 7.29/1.51  --inst_prop_sim_given                   true
% 7.29/1.51  --inst_prop_sim_new                     false
% 7.29/1.51  --inst_subs_new                         false
% 7.29/1.51  --inst_eq_res_simp                      false
% 7.29/1.51  --inst_subs_given                       false
% 7.29/1.51  --inst_orphan_elimination               true
% 7.29/1.51  --inst_learning_loop_flag               true
% 7.29/1.51  --inst_learning_start                   3000
% 7.29/1.51  --inst_learning_factor                  2
% 7.29/1.51  --inst_start_prop_sim_after_learn       3
% 7.29/1.51  --inst_sel_renew                        solver
% 7.29/1.51  --inst_lit_activity_flag                true
% 7.29/1.51  --inst_restr_to_given                   false
% 7.29/1.51  --inst_activity_threshold               500
% 7.29/1.51  --inst_out_proof                        true
% 7.29/1.51  
% 7.29/1.51  ------ Resolution Options
% 7.29/1.51  
% 7.29/1.51  --resolution_flag                       false
% 7.29/1.51  --res_lit_sel                           adaptive
% 7.29/1.51  --res_lit_sel_side                      none
% 7.29/1.51  --res_ordering                          kbo
% 7.29/1.51  --res_to_prop_solver                    active
% 7.29/1.51  --res_prop_simpl_new                    false
% 7.29/1.51  --res_prop_simpl_given                  true
% 7.29/1.51  --res_passive_queue_type                priority_queues
% 7.29/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.29/1.51  --res_passive_queues_freq               [15;5]
% 7.29/1.51  --res_forward_subs                      full
% 7.29/1.51  --res_backward_subs                     full
% 7.29/1.51  --res_forward_subs_resolution           true
% 7.29/1.51  --res_backward_subs_resolution          true
% 7.29/1.51  --res_orphan_elimination                true
% 7.29/1.51  --res_time_limit                        2.
% 7.29/1.51  --res_out_proof                         true
% 7.29/1.51  
% 7.29/1.51  ------ Superposition Options
% 7.29/1.51  
% 7.29/1.51  --superposition_flag                    true
% 7.29/1.51  --sup_passive_queue_type                priority_queues
% 7.29/1.51  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.29/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.29/1.51  --demod_completeness_check              fast
% 7.29/1.51  --demod_use_ground                      true
% 7.29/1.51  --sup_to_prop_solver                    active
% 7.29/1.51  --sup_prop_simpl_new                    false
% 7.29/1.51  --sup_prop_simpl_given                  false
% 7.29/1.51  --sup_fun_splitting                     true
% 7.29/1.51  --sup_smt_interval                      10000
% 7.29/1.51  
% 7.29/1.51  ------ Superposition Simplification Setup
% 7.29/1.51  
% 7.29/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.29/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.29/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.29/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.29/1.51  --sup_full_triv                         [TrivRules]
% 7.29/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.29/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.29/1.51  --sup_immed_triv                        [TrivRules]
% 7.29/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.29/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.29/1.51  --sup_immed_bw_main                     []
% 7.29/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.29/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.29/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.29/1.51  --sup_input_bw                          [BwDemod;BwSubsumption]
% 7.29/1.51  
% 7.29/1.51  ------ Combination Options
% 7.29/1.51  
% 7.29/1.51  --comb_res_mult                         1
% 7.29/1.51  --comb_sup_mult                         1
% 7.29/1.51  --comb_inst_mult                        1000000
% 7.29/1.51  
% 7.29/1.51  ------ Debug Options
% 7.29/1.51  
% 7.29/1.51  --dbg_backtrace                         false
% 7.29/1.51  --dbg_dump_prop_clauses                 false
% 7.29/1.51  --dbg_dump_prop_clauses_file            -
% 7.29/1.51  --dbg_out_stat                          false
% 7.29/1.51  
% 7.29/1.51  
% 7.29/1.51  
% 7.29/1.51  
% 7.29/1.51  ------ Proving...
% 7.29/1.51  
% 7.29/1.51  
% 7.29/1.51  % SZS status Theorem for theBenchmark.p
% 7.29/1.51  
% 7.29/1.51   Resolution empty clause
% 7.29/1.51  
% 7.29/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.29/1.51  
% 7.29/1.51  fof(f7,axiom,(
% 7.29/1.51    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.29/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.29/1.51  
% 7.29/1.51  fof(f21,plain,(
% 7.29/1.51    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.29/1.51    inference(cnf_transformation,[],[f7])).
% 7.29/1.51  
% 7.29/1.51  fof(f8,axiom,(
% 7.29/1.51    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 7.29/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.29/1.51  
% 7.29/1.51  fof(f22,plain,(
% 7.29/1.51    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 7.29/1.51    inference(cnf_transformation,[],[f8])).
% 7.29/1.51  
% 7.29/1.51  fof(f6,axiom,(
% 7.29/1.51    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.29/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.29/1.51  
% 7.29/1.51  fof(f20,plain,(
% 7.29/1.51    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.29/1.51    inference(cnf_transformation,[],[f6])).
% 7.29/1.51  
% 7.29/1.51  fof(f1,axiom,(
% 7.29/1.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.29/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.29/1.51  
% 7.29/1.51  fof(f15,plain,(
% 7.29/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.29/1.51    inference(cnf_transformation,[],[f1])).
% 7.29/1.51  
% 7.29/1.51  fof(f4,axiom,(
% 7.29/1.51    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 7.29/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.29/1.51  
% 7.29/1.51  fof(f18,plain,(
% 7.29/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 7.29/1.51    inference(cnf_transformation,[],[f4])).
% 7.29/1.51  
% 7.29/1.51  fof(f9,axiom,(
% 7.29/1.51    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 7.29/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.29/1.51  
% 7.29/1.51  fof(f23,plain,(
% 7.29/1.51    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 7.29/1.51    inference(cnf_transformation,[],[f9])).
% 7.29/1.51  
% 7.29/1.51  fof(f2,axiom,(
% 7.29/1.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.29/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.29/1.51  
% 7.29/1.51  fof(f16,plain,(
% 7.29/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.29/1.51    inference(cnf_transformation,[],[f2])).
% 7.29/1.51  
% 7.29/1.51  fof(f25,plain,(
% 7.29/1.51    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 7.29/1.51    inference(definition_unfolding,[],[f23,f16])).
% 7.29/1.51  
% 7.29/1.51  fof(f26,plain,(
% 7.29/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 7.29/1.51    inference(definition_unfolding,[],[f18,f25])).
% 7.29/1.51  
% 7.29/1.51  fof(f3,axiom,(
% 7.29/1.51    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 7.29/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.29/1.51  
% 7.29/1.51  fof(f17,plain,(
% 7.29/1.51    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 7.29/1.51    inference(cnf_transformation,[],[f3])).
% 7.29/1.51  
% 7.29/1.51  fof(f10,conjecture,(
% 7.29/1.51    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1)),
% 7.29/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.29/1.51  
% 7.29/1.51  fof(f11,negated_conjecture,(
% 7.29/1.51    ~! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1)),
% 7.29/1.51    inference(negated_conjecture,[],[f10])).
% 7.29/1.51  
% 7.29/1.51  fof(f12,plain,(
% 7.29/1.51    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k5_xboole_0(X0,X1)),
% 7.29/1.51    inference(ennf_transformation,[],[f11])).
% 7.29/1.51  
% 7.29/1.51  fof(f13,plain,(
% 7.29/1.51    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k5_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1)),
% 7.29/1.51    introduced(choice_axiom,[])).
% 7.29/1.51  
% 7.29/1.51  fof(f14,plain,(
% 7.29/1.51    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1)),
% 7.29/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).
% 7.29/1.51  
% 7.29/1.51  fof(f24,plain,(
% 7.29/1.51    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1)),
% 7.29/1.51    inference(cnf_transformation,[],[f14])).
% 7.29/1.51  
% 7.29/1.51  fof(f28,plain,(
% 7.29/1.51    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1)))),
% 7.29/1.51    inference(definition_unfolding,[],[f24,f16,f25])).
% 7.29/1.51  
% 7.29/1.51  fof(f5,axiom,(
% 7.29/1.51    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 7.29/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.29/1.51  
% 7.29/1.51  fof(f19,plain,(
% 7.29/1.51    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 7.29/1.51    inference(cnf_transformation,[],[f5])).
% 7.29/1.51  
% 7.29/1.51  fof(f27,plain,(
% 7.29/1.51    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 7.29/1.51    inference(definition_unfolding,[],[f19,f16,f16])).
% 7.29/1.51  
% 7.29/1.51  cnf(c_5,plain,
% 7.29/1.51      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.29/1.51      inference(cnf_transformation,[],[f21]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_6,plain,
% 7.29/1.51      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.29/1.51      inference(cnf_transformation,[],[f22]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_38,plain,
% 7.29/1.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 7.29/1.51      inference(superposition,[status(thm)],[c_5,c_6]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_36,plain,
% 7.29/1.51      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 7.29/1.51      inference(superposition,[status(thm)],[c_6,c_5]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_79,plain,
% 7.29/1.51      ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
% 7.29/1.51      inference(superposition,[status(thm)],[c_6,c_36]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_4,plain,
% 7.29/1.51      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.29/1.51      inference(cnf_transformation,[],[f20]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_94,plain,
% 7.29/1.51      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.29/1.51      inference(light_normalisation,[status(thm)],[c_79,c_4]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_95,plain,
% 7.29/1.51      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 7.29/1.51      inference(demodulation,[status(thm)],[c_94,c_36]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_143,plain,
% 7.29/1.51      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 7.29/1.51      inference(superposition,[status(thm)],[c_38,c_95]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_151,plain,
% 7.29/1.51      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 7.29/1.51      inference(demodulation,[status(thm)],[c_143,c_4]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_163,plain,
% 7.29/1.51      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 7.29/1.51      inference(superposition,[status(thm)],[c_151,c_95]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_168,plain,
% 7.29/1.51      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 7.29/1.51      inference(superposition,[status(thm)],[c_5,c_163]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_0,plain,
% 7.29/1.51      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.29/1.51      inference(cnf_transformation,[],[f15]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_2,plain,
% 7.29/1.51      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 7.29/1.51      inference(cnf_transformation,[],[f26]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_1,plain,
% 7.29/1.51      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 7.29/1.51      inference(cnf_transformation,[],[f17]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_21,plain,
% 7.29/1.51      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
% 7.29/1.51      inference(theory_normalisation,[status(thm)],[c_2,c_1,c_0]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_255,plain,
% 7.29/1.51      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 7.29/1.51      inference(superposition,[status(thm)],[c_0,c_21]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_3290,plain,
% 7.29/1.51      ( k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = X0 ),
% 7.29/1.51      inference(superposition,[status(thm)],[c_168,c_255]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_7,negated_conjecture,
% 7.29/1.51      ( k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))) ),
% 7.29/1.51      inference(cnf_transformation,[],[f28]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_19,negated_conjecture,
% 7.29/1.51      ( k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))) != k5_xboole_0(sK0,sK1) ),
% 7.29/1.51      inference(theory_normalisation,[status(thm)],[c_7,c_1,c_0]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_32,plain,
% 7.29/1.51      ( k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))) != k5_xboole_0(sK0,sK1) ),
% 7.29/1.51      inference(demodulation,[status(thm)],[c_5,c_19]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_24105,plain,
% 7.29/1.51      ( k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))) != k5_xboole_0(sK0,sK1) ),
% 7.29/1.51      inference(demodulation,[status(thm)],[c_3290,c_32]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_254,plain,
% 7.29/1.51      ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
% 7.29/1.51      inference(superposition,[status(thm)],[c_94,c_21]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_3,plain,
% 7.29/1.51      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 7.29/1.51      inference(cnf_transformation,[],[f27]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_20,plain,
% 7.29/1.51      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 7.29/1.51      inference(theory_normalisation,[status(thm)],[c_3,c_1,c_0]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_262,plain,
% 7.29/1.51      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
% 7.29/1.51      inference(superposition,[status(thm)],[c_21,c_20]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_265,plain,
% 7.29/1.51      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X1,X1)) ),
% 7.29/1.51      inference(demodulation,[status(thm)],[c_262,c_21]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_266,plain,
% 7.29/1.51      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.29/1.51      inference(demodulation,[status(thm)],[c_265,c_6]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_269,plain,
% 7.29/1.51      ( k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0)) = X0 ),
% 7.29/1.51      inference(demodulation,[status(thm)],[c_254,c_266]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_270,plain,
% 7.29/1.51      ( k3_xboole_0(X0,X0) = X0 ),
% 7.29/1.51      inference(light_normalisation,[status(thm)],[c_269,c_4]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_30,plain,
% 7.29/1.51      ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X2,k3_xboole_0(X1,X0)) ),
% 7.29/1.51      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_360,plain,
% 7.29/1.51      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
% 7.29/1.51      inference(superposition,[status(thm)],[c_270,c_30]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_516,plain,
% 7.29/1.51      ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),X0) = k3_xboole_0(X0,X0) ),
% 7.29/1.51      inference(superposition,[status(thm)],[c_21,c_360]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_565,plain,
% 7.29/1.51      ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),X0) = X0 ),
% 7.29/1.51      inference(light_normalisation,[status(thm)],[c_516,c_270]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_51,plain,
% 7.29/1.51      ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),X3)) = k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X3) ),
% 7.29/1.51      inference(superposition,[status(thm)],[c_20,c_5]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_7182,plain,
% 7.29/1.51      ( k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k3_xboole_0(X0,X2))),X3) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X2)),X3)) ),
% 7.29/1.51      inference(superposition,[status(thm)],[c_565,c_51]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_42,plain,
% 7.29/1.51      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,k3_xboole_0(X0,X2))) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
% 7.29/1.51      inference(superposition,[status(thm)],[c_0,c_20]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_843,plain,
% 7.29/1.51      ( k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X2))) = k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
% 7.29/1.51      inference(superposition,[status(thm)],[c_21,c_42]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_358,plain,
% 7.29/1.51      ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X2)) = k3_xboole_0(X2,X0) ),
% 7.29/1.51      inference(superposition,[status(thm)],[c_21,c_30]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_934,plain,
% 7.29/1.51      ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k3_xboole_0(X0,X2))) = k5_xboole_0(X0,k3_xboole_0(X2,X0)) ),
% 7.29/1.51      inference(light_normalisation,[status(thm)],[c_843,c_358]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_5667,plain,
% 7.29/1.51      ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,X2) ),
% 7.29/1.51      inference(superposition,[status(thm)],[c_565,c_1]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_7540,plain,
% 7.29/1.51      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),X2)) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X2) ),
% 7.29/1.51      inference(light_normalisation,[status(thm)],[c_7182,c_934,c_5667]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_24106,plain,
% 7.29/1.51      ( k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK0),k3_xboole_0(sK0,sK1)))) != k5_xboole_0(sK0,sK1) ),
% 7.29/1.51      inference(demodulation,[status(thm)],[c_24105,c_7540]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_885,plain,
% 7.29/1.51      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X0))) ),
% 7.29/1.51      inference(superposition,[status(thm)],[c_270,c_42]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_29,plain,
% 7.29/1.51      ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
% 7.29/1.51      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_320,plain,
% 7.29/1.51      ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
% 7.29/1.51      inference(superposition,[status(thm)],[c_270,c_29]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_439,plain,
% 7.29/1.51      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 7.29/1.51      inference(superposition,[status(thm)],[c_320,c_20]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_914,plain,
% 7.29/1.51      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X1,k1_xboole_0) ),
% 7.29/1.51      inference(light_normalisation,[status(thm)],[c_885,c_6,c_270,c_439]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_915,plain,
% 7.29/1.51      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k1_xboole_0 ),
% 7.29/1.51      inference(demodulation,[status(thm)],[c_914,c_266,c_439]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_24107,plain,
% 7.29/1.51      ( k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,sK1) ),
% 7.29/1.51      inference(demodulation,[status(thm)],[c_24106,c_4,c_915]) ).
% 7.29/1.51  
% 7.29/1.51  cnf(c_24108,plain,
% 7.29/1.51      ( $false ),
% 7.29/1.51      inference(equality_resolution_simp,[status(thm)],[c_24107]) ).
% 7.29/1.51  
% 7.29/1.51  
% 7.29/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.29/1.51  
% 7.29/1.51  ------                               Statistics
% 7.29/1.51  
% 7.29/1.51  ------ General
% 7.29/1.51  
% 7.29/1.51  abstr_ref_over_cycles:                  0
% 7.29/1.51  abstr_ref_under_cycles:                 0
% 7.29/1.51  gc_basic_clause_elim:                   0
% 7.29/1.51  forced_gc_time:                         0
% 7.29/1.51  parsing_time:                           0.012
% 7.29/1.51  unif_index_cands_time:                  0.
% 7.29/1.51  unif_index_add_time:                    0.
% 7.29/1.51  orderings_time:                         0.
% 7.29/1.51  out_proof_time:                         0.006
% 7.29/1.51  total_time:                             0.629
% 7.29/1.51  num_of_symbols:                         36
% 7.29/1.51  num_of_terms:                           34658
% 7.29/1.51  
% 7.29/1.51  ------ Preprocessing
% 7.29/1.51  
% 7.29/1.51  num_of_splits:                          0
% 7.29/1.51  num_of_split_atoms:                     0
% 7.29/1.51  num_of_reused_defs:                     0
% 7.29/1.51  num_eq_ax_congr_red:                    0
% 7.29/1.51  num_of_sem_filtered_clauses:            0
% 7.29/1.51  num_of_subtypes:                        0
% 7.29/1.51  monotx_restored_types:                  0
% 7.29/1.51  sat_num_of_epr_types:                   0
% 7.29/1.51  sat_num_of_non_cyclic_types:            0
% 7.29/1.51  sat_guarded_non_collapsed_types:        0
% 7.29/1.51  num_pure_diseq_elim:                    0
% 7.29/1.51  simp_replaced_by:                       0
% 7.29/1.51  res_preprocessed:                       20
% 7.29/1.51  prep_upred:                             0
% 7.29/1.51  prep_unflattend:                        0
% 7.29/1.51  smt_new_axioms:                         0
% 7.29/1.51  pred_elim_cands:                        0
% 7.29/1.51  pred_elim:                              0
% 7.29/1.51  pred_elim_cl:                           0
% 7.29/1.51  pred_elim_cycles:                       0
% 7.29/1.51  merged_defs:                            0
% 7.29/1.51  merged_defs_ncl:                        0
% 7.29/1.51  bin_hyper_res:                          0
% 7.29/1.51  prep_cycles:                            2
% 7.29/1.51  pred_elim_time:                         0.
% 7.29/1.51  splitting_time:                         0.
% 7.29/1.51  sem_filter_time:                        0.
% 7.29/1.51  monotx_time:                            0.
% 7.29/1.51  subtype_inf_time:                       0.
% 7.29/1.51  
% 7.29/1.51  ------ Problem properties
% 7.29/1.51  
% 7.29/1.51  clauses:                                8
% 7.29/1.51  conjectures:                            1
% 7.29/1.51  epr:                                    0
% 7.29/1.51  horn:                                   8
% 7.29/1.51  ground:                                 1
% 7.29/1.51  unary:                                  8
% 7.29/1.51  binary:                                 0
% 7.29/1.51  lits:                                   8
% 7.29/1.51  lits_eq:                                8
% 7.29/1.51  fd_pure:                                0
% 7.29/1.51  fd_pseudo:                              0
% 7.29/1.51  fd_cond:                                0
% 7.29/1.51  fd_pseudo_cond:                         0
% 7.29/1.51  ac_symbols:                             2
% 7.29/1.51  
% 7.29/1.51  ------ Propositional Solver
% 7.29/1.51  
% 7.29/1.51  prop_solver_calls:                      13
% 7.29/1.51  prop_fast_solver_calls:                 52
% 7.29/1.51  smt_solver_calls:                       0
% 7.29/1.51  smt_fast_solver_calls:                  0
% 7.29/1.51  prop_num_of_clauses:                    203
% 7.29/1.51  prop_preprocess_simplified:             331
% 7.29/1.51  prop_fo_subsumed:                       0
% 7.29/1.51  prop_solver_time:                       0.
% 7.29/1.51  smt_solver_time:                        0.
% 7.29/1.51  smt_fast_solver_time:                   0.
% 7.29/1.51  prop_fast_solver_time:                  0.
% 7.29/1.51  prop_unsat_core_time:                   0.
% 7.29/1.51  
% 7.29/1.51  ------ QBF
% 7.29/1.51  
% 7.29/1.51  qbf_q_res:                              0
% 7.29/1.51  qbf_num_tautologies:                    0
% 7.29/1.51  qbf_prep_cycles:                        0
% 7.29/1.51  
% 7.29/1.51  ------ BMC1
% 7.29/1.51  
% 7.29/1.51  bmc1_current_bound:                     -1
% 7.29/1.51  bmc1_last_solved_bound:                 -1
% 7.29/1.51  bmc1_unsat_core_size:                   -1
% 7.29/1.51  bmc1_unsat_core_parents_size:           -1
% 7.29/1.51  bmc1_merge_next_fun:                    0
% 7.29/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.29/1.51  
% 7.29/1.51  ------ Instantiation
% 7.29/1.51  
% 7.29/1.51  inst_num_of_clauses:                    0
% 7.29/1.51  inst_num_in_passive:                    0
% 7.29/1.51  inst_num_in_active:                     0
% 7.29/1.51  inst_num_in_unprocessed:                0
% 7.29/1.51  inst_num_of_loops:                      0
% 7.29/1.51  inst_num_of_learning_restarts:          0
% 7.29/1.51  inst_num_moves_active_passive:          0
% 7.29/1.51  inst_lit_activity:                      0
% 7.29/1.51  inst_lit_activity_moves:                0
% 7.29/1.51  inst_num_tautologies:                   0
% 7.29/1.51  inst_num_prop_implied:                  0
% 7.29/1.51  inst_num_existing_simplified:           0
% 7.29/1.51  inst_num_eq_res_simplified:             0
% 7.29/1.51  inst_num_child_elim:                    0
% 7.29/1.51  inst_num_of_dismatching_blockings:      0
% 7.29/1.51  inst_num_of_non_proper_insts:           0
% 7.29/1.51  inst_num_of_duplicates:                 0
% 7.29/1.51  inst_inst_num_from_inst_to_res:         0
% 7.29/1.51  inst_dismatching_checking_time:         0.
% 7.29/1.51  
% 7.29/1.51  ------ Resolution
% 7.29/1.51  
% 7.29/1.51  res_num_of_clauses:                     0
% 7.29/1.51  res_num_in_passive:                     0
% 7.29/1.51  res_num_in_active:                      0
% 7.29/1.51  res_num_of_loops:                       22
% 7.29/1.51  res_forward_subset_subsumed:            0
% 7.29/1.51  res_backward_subset_subsumed:           0
% 7.29/1.51  res_forward_subsumed:                   0
% 7.29/1.51  res_backward_subsumed:                  0
% 7.29/1.51  res_forward_subsumption_resolution:     0
% 7.29/1.51  res_backward_subsumption_resolution:    0
% 7.29/1.51  res_clause_to_clause_subsumption:       47537
% 7.29/1.51  res_orphan_elimination:                 0
% 7.29/1.51  res_tautology_del:                      0
% 7.29/1.51  res_num_eq_res_simplified:              0
% 7.29/1.51  res_num_sel_changes:                    0
% 7.29/1.51  res_moves_from_active_to_pass:          0
% 7.29/1.51  
% 7.29/1.51  ------ Superposition
% 7.29/1.51  
% 7.29/1.51  sup_time_total:                         0.
% 7.29/1.51  sup_time_generating:                    0.
% 7.29/1.51  sup_time_sim_full:                      0.
% 7.29/1.51  sup_time_sim_immed:                     0.
% 7.29/1.51  
% 7.29/1.51  sup_num_of_clauses:                     2199
% 7.29/1.51  sup_num_in_active:                      120
% 7.29/1.51  sup_num_in_passive:                     2079
% 7.29/1.51  sup_num_of_loops:                       128
% 7.29/1.51  sup_fw_superposition:                   9002
% 7.29/1.51  sup_bw_superposition:                   6205
% 7.29/1.51  sup_immediate_simplified:               7143
% 7.29/1.51  sup_given_eliminated:                   3
% 7.29/1.51  comparisons_done:                       0
% 7.29/1.51  comparisons_avoided:                    0
% 7.29/1.51  
% 7.29/1.51  ------ Simplifications
% 7.29/1.51  
% 7.29/1.51  
% 7.29/1.51  sim_fw_subset_subsumed:                 0
% 7.29/1.51  sim_bw_subset_subsumed:                 0
% 7.29/1.51  sim_fw_subsumed:                        773
% 7.29/1.51  sim_bw_subsumed:                        4
% 7.29/1.51  sim_fw_subsumption_res:                 0
% 7.29/1.51  sim_bw_subsumption_res:                 0
% 7.29/1.51  sim_tautology_del:                      0
% 7.29/1.51  sim_eq_tautology_del:                   2317
% 7.29/1.51  sim_eq_res_simp:                        0
% 7.29/1.51  sim_fw_demodulated:                     5114
% 7.29/1.51  sim_bw_demodulated:                     108
% 7.29/1.51  sim_light_normalised:                   3129
% 7.29/1.51  sim_joinable_taut:                      214
% 7.29/1.51  sim_joinable_simp:                      0
% 7.29/1.51  sim_ac_normalised:                      0
% 7.29/1.51  sim_smt_subsumption:                    0
% 7.29/1.51  
%------------------------------------------------------------------------------
