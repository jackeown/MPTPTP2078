%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:57 EST 2020

% Result     : Theorem 19.10s
% Output     : CNFRefutation 19.10s
% Verified   : 
% Statistics : Number of formulae       :  137 (2038 expanded)
%              Number of clauses        :   96 ( 920 expanded)
%              Number of leaves         :   17 ( 535 expanded)
%              Depth                    :   25
%              Number of atoms          :  138 (2039 expanded)
%              Number of equality atoms :  137 (2038 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f23,f31,f31])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f32,f31])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f36,f31])).

fof(f12,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f14,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f25,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f16,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f16])).

fof(f19,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f17])).

fof(f20,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).

fof(f37,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f41,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f37,f31])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_9,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_66,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_8])).

cnf(c_310,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9,c_66])).

cnf(c_5,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_408,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_310,c_5])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_411,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_408,c_4])).

cnf(c_420,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_411])).

cnf(c_13,plain,
    ( k2_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_374,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13,c_8])).

cnf(c_702,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_374])).

cnf(c_1332,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_702])).

cnf(c_288,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_9])).

cnf(c_16213,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X1,X0),X0))),k1_xboole_0) = k5_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_1332,c_288])).

cnf(c_16217,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X1,X0),X0))) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X1,X0),X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1332,c_1])).

cnf(c_10,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_11,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_41,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_11,c_2])).

cnf(c_223,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_10,c_41])).

cnf(c_699,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(k1_xboole_0,k5_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_223,c_374])).

cnf(c_43,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_733,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_699,c_43])).

cnf(c_72,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_8,c_5])).

cnf(c_76,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_72,c_4])).

cnf(c_437,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_76])).

cnf(c_945,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_437,c_8])).

cnf(c_7,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_271,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_7,c_5])).

cnf(c_11390,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X1)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_945,c_271])).

cnf(c_11515,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_11390,c_4])).

cnf(c_128,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_66,c_5])).

cnf(c_129,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_128,c_4])).

cnf(c_525,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_129,c_0])).

cnf(c_11630,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X0) = k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X1)) ),
    inference(superposition,[status(thm)],[c_11515,c_525])).

cnf(c_11661,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X0) = X0 ),
    inference(demodulation,[status(thm)],[c_11630,c_11515])).

cnf(c_259,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_7])).

cnf(c_12526,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X0))),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_11661,c_259])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_12537,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_12526,c_6,c_66])).

cnf(c_13583,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_12537,c_1])).

cnf(c_13601,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_13583,c_6,c_8])).

cnf(c_13737,plain,
    ( k4_xboole_0(k2_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)),k1_xboole_0) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_733,c_13601])).

cnf(c_712,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_411,c_374])).

cnf(c_1763,plain,
    ( k2_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_712,c_5])).

cnf(c_1766,plain,
    ( k2_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1763,c_4])).

cnf(c_2305,plain,
    ( k2_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_1766,c_525])).

cnf(c_2316,plain,
    ( k2_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = X0 ),
    inference(demodulation,[status(thm)],[c_2305,c_1766])).

cnf(c_2777,plain,
    ( k2_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0),k5_xboole_0(X0,X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_733,c_2316])).

cnf(c_12,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_40,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_11,c_2])).

cnf(c_57,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_12,c_40])).

cnf(c_60,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_57,c_10])).

cnf(c_114,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
    inference(superposition,[status(thm)],[c_60,c_60])).

cnf(c_558,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_223,c_114])).

cnf(c_2811,plain,
    ( k2_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = k5_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_2777,c_558])).

cnf(c_13825,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) = k5_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_13737,c_2811])).

cnf(c_16232,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X1,X0),X0))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_16217,c_13825])).

cnf(c_16236,plain,
    ( k2_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0) = k5_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(demodulation,[status(thm)],[c_16213,c_16232])).

cnf(c_931,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_5,c_437])).

cnf(c_126,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_66])).

cnf(c_488,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_126,c_5])).

cnf(c_491,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_488,c_4])).

cnf(c_966,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_931,c_491])).

cnf(c_13527,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_966,c_12537])).

cnf(c_13636,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_13527,c_13601])).

cnf(c_14451,plain,
    ( k2_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_13636,c_13])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_68,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3,c_8])).

cnf(c_514,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_129])).

cnf(c_1037,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_5,c_514])).

cnf(c_1075,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1037,c_514])).

cnf(c_2622,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1075,c_0])).

cnf(c_14495,plain,
    ( k2_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_14451,c_68,c_2622])).

cnf(c_16237,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_16236,c_14495])).

cnf(c_107,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(superposition,[status(thm)],[c_2,c_60])).

cnf(c_139,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
    inference(superposition,[status(thm)],[c_107,c_60])).

cnf(c_19139,plain,
    ( k5_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_16237,c_139])).

cnf(c_19856,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_420,c_19139])).

cnf(c_406,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_310,c_1])).

cnf(c_412,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_406,c_4,c_7])).

cnf(c_7554,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_412])).

cnf(c_20027,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_19856,c_7554])).

cnf(c_14,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_32,negated_conjecture,
    ( k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
    inference(theory_normalisation,[status(thm)],[c_14,c_11,c_2])).

cnf(c_90330,plain,
    ( k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_20027,c_32])).

cnf(c_13526,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1075,c_12537])).

cnf(c_13637,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_13526,c_13636])).

cnf(c_19100,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_13637,c_16237])).

cnf(c_7852,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_491])).

cnf(c_19251,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_19100,c_7852])).

cnf(c_90331,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_90330,c_19251])).

cnf(c_90332,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_90331])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:25:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 19.10/2.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.10/2.99  
% 19.10/2.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.10/2.99  
% 19.10/2.99  ------  iProver source info
% 19.10/2.99  
% 19.10/2.99  git: date: 2020-06-30 10:37:57 +0100
% 19.10/2.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.10/2.99  git: non_committed_changes: false
% 19.10/2.99  git: last_make_outside_of_git: false
% 19.10/2.99  
% 19.10/2.99  ------ 
% 19.10/2.99  
% 19.10/2.99  ------ Input Options
% 19.10/2.99  
% 19.10/2.99  --out_options                           all
% 19.10/2.99  --tptp_safe_out                         true
% 19.10/2.99  --problem_path                          ""
% 19.10/2.99  --include_path                          ""
% 19.10/2.99  --clausifier                            res/vclausify_rel
% 19.10/2.99  --clausifier_options                    --mode clausify
% 19.10/2.99  --stdin                                 false
% 19.10/2.99  --stats_out                             all
% 19.10/2.99  
% 19.10/2.99  ------ General Options
% 19.10/2.99  
% 19.10/2.99  --fof                                   false
% 19.10/2.99  --time_out_real                         305.
% 19.10/2.99  --time_out_virtual                      -1.
% 19.10/2.99  --symbol_type_check                     false
% 19.10/2.99  --clausify_out                          false
% 19.10/2.99  --sig_cnt_out                           false
% 19.10/2.99  --trig_cnt_out                          false
% 19.10/2.99  --trig_cnt_out_tolerance                1.
% 19.10/2.99  --trig_cnt_out_sk_spl                   false
% 19.10/2.99  --abstr_cl_out                          false
% 19.10/2.99  
% 19.10/2.99  ------ Global Options
% 19.10/2.99  
% 19.10/2.99  --schedule                              default
% 19.10/2.99  --add_important_lit                     false
% 19.10/2.99  --prop_solver_per_cl                    1000
% 19.10/2.99  --min_unsat_core                        false
% 19.10/2.99  --soft_assumptions                      false
% 19.10/2.99  --soft_lemma_size                       3
% 19.10/2.99  --prop_impl_unit_size                   0
% 19.10/2.99  --prop_impl_unit                        []
% 19.10/2.99  --share_sel_clauses                     true
% 19.10/2.99  --reset_solvers                         false
% 19.10/2.99  --bc_imp_inh                            [conj_cone]
% 19.10/2.99  --conj_cone_tolerance                   3.
% 19.10/2.99  --extra_neg_conj                        none
% 19.10/2.99  --large_theory_mode                     true
% 19.10/2.99  --prolific_symb_bound                   200
% 19.10/2.99  --lt_threshold                          2000
% 19.10/2.99  --clause_weak_htbl                      true
% 19.10/2.99  --gc_record_bc_elim                     false
% 19.10/2.99  
% 19.10/2.99  ------ Preprocessing Options
% 19.10/2.99  
% 19.10/2.99  --preprocessing_flag                    true
% 19.10/2.99  --time_out_prep_mult                    0.1
% 19.10/2.99  --splitting_mode                        input
% 19.10/2.99  --splitting_grd                         true
% 19.10/2.99  --splitting_cvd                         false
% 19.10/2.99  --splitting_cvd_svl                     false
% 19.10/2.99  --splitting_nvd                         32
% 19.10/2.99  --sub_typing                            true
% 19.10/2.99  --prep_gs_sim                           true
% 19.10/2.99  --prep_unflatten                        true
% 19.10/2.99  --prep_res_sim                          true
% 19.10/2.99  --prep_upred                            true
% 19.10/2.99  --prep_sem_filter                       exhaustive
% 19.10/2.99  --prep_sem_filter_out                   false
% 19.10/2.99  --pred_elim                             true
% 19.10/2.99  --res_sim_input                         true
% 19.10/2.99  --eq_ax_congr_red                       true
% 19.10/2.99  --pure_diseq_elim                       true
% 19.10/2.99  --brand_transform                       false
% 19.10/2.99  --non_eq_to_eq                          false
% 19.10/2.99  --prep_def_merge                        true
% 19.10/2.99  --prep_def_merge_prop_impl              false
% 19.10/2.99  --prep_def_merge_mbd                    true
% 19.10/2.99  --prep_def_merge_tr_red                 false
% 19.10/2.99  --prep_def_merge_tr_cl                  false
% 19.10/2.99  --smt_preprocessing                     true
% 19.10/2.99  --smt_ac_axioms                         fast
% 19.10/2.99  --preprocessed_out                      false
% 19.10/2.99  --preprocessed_stats                    false
% 19.10/2.99  
% 19.10/2.99  ------ Abstraction refinement Options
% 19.10/2.99  
% 19.10/2.99  --abstr_ref                             []
% 19.10/2.99  --abstr_ref_prep                        false
% 19.10/2.99  --abstr_ref_until_sat                   false
% 19.10/2.99  --abstr_ref_sig_restrict                funpre
% 19.10/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.10/2.99  --abstr_ref_under                       []
% 19.10/2.99  
% 19.10/2.99  ------ SAT Options
% 19.10/2.99  
% 19.10/2.99  --sat_mode                              false
% 19.10/2.99  --sat_fm_restart_options                ""
% 19.10/2.99  --sat_gr_def                            false
% 19.10/2.99  --sat_epr_types                         true
% 19.10/2.99  --sat_non_cyclic_types                  false
% 19.10/2.99  --sat_finite_models                     false
% 19.10/2.99  --sat_fm_lemmas                         false
% 19.10/2.99  --sat_fm_prep                           false
% 19.10/2.99  --sat_fm_uc_incr                        true
% 19.10/2.99  --sat_out_model                         small
% 19.10/2.99  --sat_out_clauses                       false
% 19.10/2.99  
% 19.10/2.99  ------ QBF Options
% 19.10/2.99  
% 19.10/2.99  --qbf_mode                              false
% 19.10/2.99  --qbf_elim_univ                         false
% 19.10/2.99  --qbf_dom_inst                          none
% 19.10/2.99  --qbf_dom_pre_inst                      false
% 19.10/2.99  --qbf_sk_in                             false
% 19.10/2.99  --qbf_pred_elim                         true
% 19.10/2.99  --qbf_split                             512
% 19.10/2.99  
% 19.10/2.99  ------ BMC1 Options
% 19.10/2.99  
% 19.10/2.99  --bmc1_incremental                      false
% 19.10/2.99  --bmc1_axioms                           reachable_all
% 19.10/2.99  --bmc1_min_bound                        0
% 19.10/2.99  --bmc1_max_bound                        -1
% 19.10/2.99  --bmc1_max_bound_default                -1
% 19.10/2.99  --bmc1_symbol_reachability              true
% 19.10/2.99  --bmc1_property_lemmas                  false
% 19.10/2.99  --bmc1_k_induction                      false
% 19.10/2.99  --bmc1_non_equiv_states                 false
% 19.10/2.99  --bmc1_deadlock                         false
% 19.10/2.99  --bmc1_ucm                              false
% 19.10/2.99  --bmc1_add_unsat_core                   none
% 19.10/2.99  --bmc1_unsat_core_children              false
% 19.10/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.10/2.99  --bmc1_out_stat                         full
% 19.10/2.99  --bmc1_ground_init                      false
% 19.10/2.99  --bmc1_pre_inst_next_state              false
% 19.10/2.99  --bmc1_pre_inst_state                   false
% 19.10/2.99  --bmc1_pre_inst_reach_state             false
% 19.10/2.99  --bmc1_out_unsat_core                   false
% 19.10/2.99  --bmc1_aig_witness_out                  false
% 19.10/2.99  --bmc1_verbose                          false
% 19.10/2.99  --bmc1_dump_clauses_tptp                false
% 19.10/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.10/2.99  --bmc1_dump_file                        -
% 19.10/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.10/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.10/2.99  --bmc1_ucm_extend_mode                  1
% 19.10/2.99  --bmc1_ucm_init_mode                    2
% 19.10/2.99  --bmc1_ucm_cone_mode                    none
% 19.10/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.10/2.99  --bmc1_ucm_relax_model                  4
% 19.10/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.10/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.10/2.99  --bmc1_ucm_layered_model                none
% 19.10/2.99  --bmc1_ucm_max_lemma_size               10
% 19.10/2.99  
% 19.10/2.99  ------ AIG Options
% 19.10/2.99  
% 19.10/2.99  --aig_mode                              false
% 19.10/2.99  
% 19.10/2.99  ------ Instantiation Options
% 19.10/2.99  
% 19.10/2.99  --instantiation_flag                    true
% 19.10/2.99  --inst_sos_flag                         false
% 19.10/2.99  --inst_sos_phase                        true
% 19.10/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.10/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.10/2.99  --inst_lit_sel_side                     num_symb
% 19.10/2.99  --inst_solver_per_active                1400
% 19.10/2.99  --inst_solver_calls_frac                1.
% 19.10/2.99  --inst_passive_queue_type               priority_queues
% 19.10/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.10/2.99  --inst_passive_queues_freq              [25;2]
% 19.10/2.99  --inst_dismatching                      true
% 19.10/2.99  --inst_eager_unprocessed_to_passive     true
% 19.10/2.99  --inst_prop_sim_given                   true
% 19.10/2.99  --inst_prop_sim_new                     false
% 19.10/2.99  --inst_subs_new                         false
% 19.10/2.99  --inst_eq_res_simp                      false
% 19.10/2.99  --inst_subs_given                       false
% 19.10/2.99  --inst_orphan_elimination               true
% 19.10/2.99  --inst_learning_loop_flag               true
% 19.10/2.99  --inst_learning_start                   3000
% 19.10/2.99  --inst_learning_factor                  2
% 19.10/2.99  --inst_start_prop_sim_after_learn       3
% 19.10/2.99  --inst_sel_renew                        solver
% 19.10/2.99  --inst_lit_activity_flag                true
% 19.10/2.99  --inst_restr_to_given                   false
% 19.10/2.99  --inst_activity_threshold               500
% 19.10/2.99  --inst_out_proof                        true
% 19.10/2.99  
% 19.10/2.99  ------ Resolution Options
% 19.10/2.99  
% 19.10/2.99  --resolution_flag                       true
% 19.10/2.99  --res_lit_sel                           adaptive
% 19.10/2.99  --res_lit_sel_side                      none
% 19.10/2.99  --res_ordering                          kbo
% 19.10/2.99  --res_to_prop_solver                    active
% 19.10/2.99  --res_prop_simpl_new                    false
% 19.10/2.99  --res_prop_simpl_given                  true
% 19.10/2.99  --res_passive_queue_type                priority_queues
% 19.10/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.10/2.99  --res_passive_queues_freq               [15;5]
% 19.10/2.99  --res_forward_subs                      full
% 19.10/2.99  --res_backward_subs                     full
% 19.10/2.99  --res_forward_subs_resolution           true
% 19.10/2.99  --res_backward_subs_resolution          true
% 19.10/2.99  --res_orphan_elimination                true
% 19.10/2.99  --res_time_limit                        2.
% 19.10/2.99  --res_out_proof                         true
% 19.10/2.99  
% 19.10/2.99  ------ Superposition Options
% 19.10/2.99  
% 19.10/2.99  --superposition_flag                    true
% 19.10/2.99  --sup_passive_queue_type                priority_queues
% 19.10/2.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.10/2.99  --sup_passive_queues_freq               [8;1;4]
% 19.10/2.99  --demod_completeness_check              fast
% 19.10/2.99  --demod_use_ground                      true
% 19.10/2.99  --sup_to_prop_solver                    passive
% 19.10/2.99  --sup_prop_simpl_new                    true
% 19.10/2.99  --sup_prop_simpl_given                  true
% 19.10/2.99  --sup_fun_splitting                     false
% 19.10/2.99  --sup_smt_interval                      50000
% 19.10/2.99  
% 19.10/2.99  ------ Superposition Simplification Setup
% 19.10/2.99  
% 19.10/2.99  --sup_indices_passive                   []
% 19.10/2.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.10/2.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.10/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.10/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.10/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.10/2.99  --sup_full_bw                           [BwDemod]
% 19.10/2.99  --sup_immed_triv                        [TrivRules]
% 19.10/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.10/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.10/2.99  --sup_immed_bw_main                     []
% 19.10/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.10/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.10/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.10/2.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.10/2.99  
% 19.10/2.99  ------ Combination Options
% 19.10/2.99  
% 19.10/2.99  --comb_res_mult                         3
% 19.10/2.99  --comb_sup_mult                         2
% 19.10/2.99  --comb_inst_mult                        10
% 19.10/2.99  
% 19.10/2.99  ------ Debug Options
% 19.10/2.99  
% 19.10/2.99  --dbg_backtrace                         false
% 19.10/2.99  --dbg_dump_prop_clauses                 false
% 19.10/2.99  --dbg_dump_prop_clauses_file            -
% 19.10/2.99  --dbg_out_stat                          false
% 19.10/2.99  ------ Parsing...
% 19.10/2.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.10/2.99  
% 19.10/2.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 19.10/2.99  
% 19.10/2.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.10/2.99  
% 19.10/2.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.10/2.99  ------ Proving...
% 19.10/2.99  ------ Problem Properties 
% 19.10/2.99  
% 19.10/2.99  
% 19.10/2.99  clauses                                 15
% 19.10/2.99  conjectures                             1
% 19.10/2.99  EPR                                     0
% 19.10/2.99  Horn                                    15
% 19.10/2.99  unary                                   15
% 19.10/2.99  binary                                  0
% 19.10/2.99  lits                                    15
% 19.10/2.99  lits eq                                 15
% 19.10/2.99  fd_pure                                 0
% 19.10/2.99  fd_pseudo                               0
% 19.10/2.99  fd_cond                                 0
% 19.10/2.99  fd_pseudo_cond                          0
% 19.10/2.99  AC symbols                              1
% 19.10/2.99  
% 19.10/2.99  ------ Schedule UEQ
% 19.10/2.99  
% 19.10/2.99  ------ pure equality problem: resolution off 
% 19.10/2.99  
% 19.10/2.99  ------ Option_UEQ Time Limit: Unbounded
% 19.10/2.99  
% 19.10/2.99  
% 19.10/2.99  ------ 
% 19.10/2.99  Current options:
% 19.10/2.99  ------ 
% 19.10/2.99  
% 19.10/2.99  ------ Input Options
% 19.10/2.99  
% 19.10/2.99  --out_options                           all
% 19.10/2.99  --tptp_safe_out                         true
% 19.10/2.99  --problem_path                          ""
% 19.10/2.99  --include_path                          ""
% 19.10/2.99  --clausifier                            res/vclausify_rel
% 19.10/2.99  --clausifier_options                    --mode clausify
% 19.10/2.99  --stdin                                 false
% 19.10/2.99  --stats_out                             all
% 19.10/2.99  
% 19.10/2.99  ------ General Options
% 19.10/2.99  
% 19.10/2.99  --fof                                   false
% 19.10/2.99  --time_out_real                         305.
% 19.10/2.99  --time_out_virtual                      -1.
% 19.10/2.99  --symbol_type_check                     false
% 19.10/2.99  --clausify_out                          false
% 19.10/2.99  --sig_cnt_out                           false
% 19.10/2.99  --trig_cnt_out                          false
% 19.10/2.99  --trig_cnt_out_tolerance                1.
% 19.10/2.99  --trig_cnt_out_sk_spl                   false
% 19.10/2.99  --abstr_cl_out                          false
% 19.10/2.99  
% 19.10/2.99  ------ Global Options
% 19.10/2.99  
% 19.10/2.99  --schedule                              default
% 19.10/2.99  --add_important_lit                     false
% 19.10/2.99  --prop_solver_per_cl                    1000
% 19.10/2.99  --min_unsat_core                        false
% 19.10/2.99  --soft_assumptions                      false
% 19.10/2.99  --soft_lemma_size                       3
% 19.10/2.99  --prop_impl_unit_size                   0
% 19.10/2.99  --prop_impl_unit                        []
% 19.10/2.99  --share_sel_clauses                     true
% 19.10/2.99  --reset_solvers                         false
% 19.10/2.99  --bc_imp_inh                            [conj_cone]
% 19.10/2.99  --conj_cone_tolerance                   3.
% 19.10/2.99  --extra_neg_conj                        none
% 19.10/2.99  --large_theory_mode                     true
% 19.10/2.99  --prolific_symb_bound                   200
% 19.10/2.99  --lt_threshold                          2000
% 19.10/2.99  --clause_weak_htbl                      true
% 19.10/2.99  --gc_record_bc_elim                     false
% 19.10/2.99  
% 19.10/2.99  ------ Preprocessing Options
% 19.10/2.99  
% 19.10/2.99  --preprocessing_flag                    true
% 19.10/2.99  --time_out_prep_mult                    0.1
% 19.10/2.99  --splitting_mode                        input
% 19.10/2.99  --splitting_grd                         true
% 19.10/2.99  --splitting_cvd                         false
% 19.10/2.99  --splitting_cvd_svl                     false
% 19.10/2.99  --splitting_nvd                         32
% 19.10/2.99  --sub_typing                            true
% 19.10/2.99  --prep_gs_sim                           true
% 19.10/2.99  --prep_unflatten                        true
% 19.10/2.99  --prep_res_sim                          true
% 19.10/2.99  --prep_upred                            true
% 19.10/2.99  --prep_sem_filter                       exhaustive
% 19.10/2.99  --prep_sem_filter_out                   false
% 19.10/2.99  --pred_elim                             true
% 19.10/2.99  --res_sim_input                         true
% 19.10/2.99  --eq_ax_congr_red                       true
% 19.10/2.99  --pure_diseq_elim                       true
% 19.10/2.99  --brand_transform                       false
% 19.10/2.99  --non_eq_to_eq                          false
% 19.10/2.99  --prep_def_merge                        true
% 19.10/2.99  --prep_def_merge_prop_impl              false
% 19.10/2.99  --prep_def_merge_mbd                    true
% 19.10/2.99  --prep_def_merge_tr_red                 false
% 19.10/2.99  --prep_def_merge_tr_cl                  false
% 19.10/2.99  --smt_preprocessing                     true
% 19.10/2.99  --smt_ac_axioms                         fast
% 19.10/2.99  --preprocessed_out                      false
% 19.10/2.99  --preprocessed_stats                    false
% 19.10/2.99  
% 19.10/2.99  ------ Abstraction refinement Options
% 19.10/2.99  
% 19.10/2.99  --abstr_ref                             []
% 19.10/2.99  --abstr_ref_prep                        false
% 19.10/2.99  --abstr_ref_until_sat                   false
% 19.10/2.99  --abstr_ref_sig_restrict                funpre
% 19.10/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.10/2.99  --abstr_ref_under                       []
% 19.10/2.99  
% 19.10/2.99  ------ SAT Options
% 19.10/2.99  
% 19.10/2.99  --sat_mode                              false
% 19.10/2.99  --sat_fm_restart_options                ""
% 19.10/2.99  --sat_gr_def                            false
% 19.10/2.99  --sat_epr_types                         true
% 19.10/2.99  --sat_non_cyclic_types                  false
% 19.10/2.99  --sat_finite_models                     false
% 19.10/2.99  --sat_fm_lemmas                         false
% 19.10/2.99  --sat_fm_prep                           false
% 19.10/2.99  --sat_fm_uc_incr                        true
% 19.10/2.99  --sat_out_model                         small
% 19.10/2.99  --sat_out_clauses                       false
% 19.10/2.99  
% 19.10/2.99  ------ QBF Options
% 19.10/2.99  
% 19.10/2.99  --qbf_mode                              false
% 19.10/2.99  --qbf_elim_univ                         false
% 19.10/2.99  --qbf_dom_inst                          none
% 19.10/2.99  --qbf_dom_pre_inst                      false
% 19.10/2.99  --qbf_sk_in                             false
% 19.10/2.99  --qbf_pred_elim                         true
% 19.10/2.99  --qbf_split                             512
% 19.10/2.99  
% 19.10/2.99  ------ BMC1 Options
% 19.10/2.99  
% 19.10/2.99  --bmc1_incremental                      false
% 19.10/2.99  --bmc1_axioms                           reachable_all
% 19.10/2.99  --bmc1_min_bound                        0
% 19.10/2.99  --bmc1_max_bound                        -1
% 19.10/2.99  --bmc1_max_bound_default                -1
% 19.10/2.99  --bmc1_symbol_reachability              true
% 19.10/2.99  --bmc1_property_lemmas                  false
% 19.10/2.99  --bmc1_k_induction                      false
% 19.10/2.99  --bmc1_non_equiv_states                 false
% 19.10/2.99  --bmc1_deadlock                         false
% 19.10/2.99  --bmc1_ucm                              false
% 19.10/2.99  --bmc1_add_unsat_core                   none
% 19.10/2.99  --bmc1_unsat_core_children              false
% 19.10/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.10/2.99  --bmc1_out_stat                         full
% 19.10/2.99  --bmc1_ground_init                      false
% 19.10/2.99  --bmc1_pre_inst_next_state              false
% 19.10/2.99  --bmc1_pre_inst_state                   false
% 19.10/2.99  --bmc1_pre_inst_reach_state             false
% 19.10/2.99  --bmc1_out_unsat_core                   false
% 19.10/2.99  --bmc1_aig_witness_out                  false
% 19.10/2.99  --bmc1_verbose                          false
% 19.10/2.99  --bmc1_dump_clauses_tptp                false
% 19.10/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.10/2.99  --bmc1_dump_file                        -
% 19.10/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.10/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.10/2.99  --bmc1_ucm_extend_mode                  1
% 19.10/2.99  --bmc1_ucm_init_mode                    2
% 19.10/2.99  --bmc1_ucm_cone_mode                    none
% 19.10/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.10/2.99  --bmc1_ucm_relax_model                  4
% 19.10/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.10/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.10/2.99  --bmc1_ucm_layered_model                none
% 19.10/2.99  --bmc1_ucm_max_lemma_size               10
% 19.10/2.99  
% 19.10/2.99  ------ AIG Options
% 19.10/2.99  
% 19.10/2.99  --aig_mode                              false
% 19.10/2.99  
% 19.10/2.99  ------ Instantiation Options
% 19.10/2.99  
% 19.10/2.99  --instantiation_flag                    false
% 19.10/2.99  --inst_sos_flag                         false
% 19.10/2.99  --inst_sos_phase                        true
% 19.10/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.10/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.10/2.99  --inst_lit_sel_side                     num_symb
% 19.10/2.99  --inst_solver_per_active                1400
% 19.10/2.99  --inst_solver_calls_frac                1.
% 19.10/2.99  --inst_passive_queue_type               priority_queues
% 19.10/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.10/2.99  --inst_passive_queues_freq              [25;2]
% 19.10/2.99  --inst_dismatching                      true
% 19.10/2.99  --inst_eager_unprocessed_to_passive     true
% 19.10/2.99  --inst_prop_sim_given                   true
% 19.10/2.99  --inst_prop_sim_new                     false
% 19.10/2.99  --inst_subs_new                         false
% 19.10/2.99  --inst_eq_res_simp                      false
% 19.10/2.99  --inst_subs_given                       false
% 19.10/2.99  --inst_orphan_elimination               true
% 19.10/2.99  --inst_learning_loop_flag               true
% 19.10/2.99  --inst_learning_start                   3000
% 19.10/2.99  --inst_learning_factor                  2
% 19.10/2.99  --inst_start_prop_sim_after_learn       3
% 19.10/2.99  --inst_sel_renew                        solver
% 19.10/2.99  --inst_lit_activity_flag                true
% 19.10/2.99  --inst_restr_to_given                   false
% 19.10/2.99  --inst_activity_threshold               500
% 19.10/2.99  --inst_out_proof                        true
% 19.10/2.99  
% 19.10/2.99  ------ Resolution Options
% 19.10/2.99  
% 19.10/2.99  --resolution_flag                       false
% 19.10/2.99  --res_lit_sel                           adaptive
% 19.10/2.99  --res_lit_sel_side                      none
% 19.10/2.99  --res_ordering                          kbo
% 19.10/2.99  --res_to_prop_solver                    active
% 19.10/2.99  --res_prop_simpl_new                    false
% 19.10/2.99  --res_prop_simpl_given                  true
% 19.10/2.99  --res_passive_queue_type                priority_queues
% 19.10/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.10/2.99  --res_passive_queues_freq               [15;5]
% 19.10/2.99  --res_forward_subs                      full
% 19.10/2.99  --res_backward_subs                     full
% 19.10/2.99  --res_forward_subs_resolution           true
% 19.10/2.99  --res_backward_subs_resolution          true
% 19.10/2.99  --res_orphan_elimination                true
% 19.10/2.99  --res_time_limit                        2.
% 19.10/2.99  --res_out_proof                         true
% 19.10/2.99  
% 19.10/2.99  ------ Superposition Options
% 19.10/2.99  
% 19.10/2.99  --superposition_flag                    true
% 19.10/2.99  --sup_passive_queue_type                priority_queues
% 19.10/2.99  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.10/2.99  --sup_passive_queues_freq               [8;1;4]
% 19.10/2.99  --demod_completeness_check              fast
% 19.10/2.99  --demod_use_ground                      true
% 19.10/2.99  --sup_to_prop_solver                    active
% 19.10/2.99  --sup_prop_simpl_new                    false
% 19.10/2.99  --sup_prop_simpl_given                  false
% 19.10/2.99  --sup_fun_splitting                     true
% 19.10/2.99  --sup_smt_interval                      10000
% 19.10/2.99  
% 19.10/2.99  ------ Superposition Simplification Setup
% 19.10/2.99  
% 19.10/2.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.10/2.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.10/2.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.10/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.10/2.99  --sup_full_triv                         [TrivRules]
% 19.10/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.10/2.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.10/2.99  --sup_immed_triv                        [TrivRules]
% 19.10/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.10/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.10/2.99  --sup_immed_bw_main                     []
% 19.10/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.10/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.10/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.10/2.99  --sup_input_bw                          [BwDemod;BwSubsumption]
% 19.10/2.99  
% 19.10/2.99  ------ Combination Options
% 19.10/2.99  
% 19.10/2.99  --comb_res_mult                         1
% 19.10/2.99  --comb_sup_mult                         1
% 19.10/2.99  --comb_inst_mult                        1000000
% 19.10/2.99  
% 19.10/2.99  ------ Debug Options
% 19.10/2.99  
% 19.10/2.99  --dbg_backtrace                         false
% 19.10/2.99  --dbg_dump_prop_clauses                 false
% 19.10/2.99  --dbg_dump_prop_clauses_file            -
% 19.10/2.99  --dbg_out_stat                          false
% 19.10/2.99  
% 19.10/2.99  
% 19.10/2.99  
% 19.10/2.99  
% 19.10/2.99  ------ Proving...
% 19.10/2.99  
% 19.10/2.99  
% 19.10/2.99  % SZS status Theorem for theBenchmark.p
% 19.10/2.99  
% 19.10/2.99   Resolution empty clause
% 19.10/2.99  
% 19.10/2.99  % SZS output start CNFRefutation for theBenchmark.p
% 19.10/2.99  
% 19.10/2.99  fof(f2,axiom,(
% 19.10/2.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 19.10/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.10/2.99  
% 19.10/2.99  fof(f23,plain,(
% 19.10/2.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 19.10/2.99    inference(cnf_transformation,[],[f2])).
% 19.10/2.99  
% 19.10/2.99  fof(f10,axiom,(
% 19.10/2.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 19.10/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.10/2.99  
% 19.10/2.99  fof(f31,plain,(
% 19.10/2.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 19.10/2.99    inference(cnf_transformation,[],[f10])).
% 19.10/2.99  
% 19.10/2.99  fof(f38,plain,(
% 19.10/2.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 19.10/2.99    inference(definition_unfolding,[],[f23,f31,f31])).
% 19.10/2.99  
% 19.10/2.99  fof(f11,axiom,(
% 19.10/2.99    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 19.10/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.10/2.99  
% 19.10/2.99  fof(f32,plain,(
% 19.10/2.99    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 19.10/2.99    inference(cnf_transformation,[],[f11])).
% 19.10/2.99  
% 19.10/2.99  fof(f39,plain,(
% 19.10/2.99    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 19.10/2.99    inference(definition_unfolding,[],[f32,f31])).
% 19.10/2.99  
% 19.10/2.99  fof(f1,axiom,(
% 19.10/2.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 19.10/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.10/2.99  
% 19.10/2.99  fof(f22,plain,(
% 19.10/2.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 19.10/2.99    inference(cnf_transformation,[],[f1])).
% 19.10/2.99  
% 19.10/2.99  fof(f9,axiom,(
% 19.10/2.99    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 19.10/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.10/2.99  
% 19.10/2.99  fof(f30,plain,(
% 19.10/2.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 19.10/2.99    inference(cnf_transformation,[],[f9])).
% 19.10/2.99  
% 19.10/2.99  fof(f6,axiom,(
% 19.10/2.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 19.10/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.10/2.99  
% 19.10/2.99  fof(f27,plain,(
% 19.10/2.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 19.10/2.99    inference(cnf_transformation,[],[f6])).
% 19.10/2.99  
% 19.10/2.99  fof(f5,axiom,(
% 19.10/2.99    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 19.10/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.10/2.99  
% 19.10/2.99  fof(f26,plain,(
% 19.10/2.99    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 19.10/2.99    inference(cnf_transformation,[],[f5])).
% 19.10/2.99  
% 19.10/2.99  fof(f15,axiom,(
% 19.10/2.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 19.10/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.10/2.99  
% 19.10/2.99  fof(f36,plain,(
% 19.10/2.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 19.10/2.99    inference(cnf_transformation,[],[f15])).
% 19.10/2.99  
% 19.10/2.99  fof(f40,plain,(
% 19.10/2.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 19.10/2.99    inference(definition_unfolding,[],[f36,f31])).
% 19.10/2.99  
% 19.10/2.99  fof(f12,axiom,(
% 19.10/2.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 19.10/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.10/2.99  
% 19.10/2.99  fof(f33,plain,(
% 19.10/2.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 19.10/2.99    inference(cnf_transformation,[],[f12])).
% 19.10/2.99  
% 19.10/2.99  fof(f13,axiom,(
% 19.10/2.99    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 19.10/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.10/2.99  
% 19.10/2.99  fof(f34,plain,(
% 19.10/2.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 19.10/2.99    inference(cnf_transformation,[],[f13])).
% 19.10/2.99  
% 19.10/2.99  fof(f3,axiom,(
% 19.10/2.99    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 19.10/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.10/2.99  
% 19.10/2.99  fof(f24,plain,(
% 19.10/2.99    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 19.10/2.99    inference(cnf_transformation,[],[f3])).
% 19.10/2.99  
% 19.10/2.99  fof(f8,axiom,(
% 19.10/2.99    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 19.10/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.10/2.99  
% 19.10/2.99  fof(f29,plain,(
% 19.10/2.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 19.10/2.99    inference(cnf_transformation,[],[f8])).
% 19.10/2.99  
% 19.10/2.99  fof(f7,axiom,(
% 19.10/2.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 19.10/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.10/2.99  
% 19.10/2.99  fof(f28,plain,(
% 19.10/2.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 19.10/2.99    inference(cnf_transformation,[],[f7])).
% 19.10/2.99  
% 19.10/2.99  fof(f14,axiom,(
% 19.10/2.99    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 19.10/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.10/2.99  
% 19.10/2.99  fof(f35,plain,(
% 19.10/2.99    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 19.10/2.99    inference(cnf_transformation,[],[f14])).
% 19.10/2.99  
% 19.10/2.99  fof(f4,axiom,(
% 19.10/2.99    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 19.10/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.10/2.99  
% 19.10/2.99  fof(f18,plain,(
% 19.10/2.99    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 19.10/2.99    inference(rectify,[],[f4])).
% 19.10/2.99  
% 19.10/2.99  fof(f25,plain,(
% 19.10/2.99    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 19.10/2.99    inference(cnf_transformation,[],[f18])).
% 19.10/2.99  
% 19.10/2.99  fof(f16,conjecture,(
% 19.10/2.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 19.10/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.10/2.99  
% 19.10/2.99  fof(f17,negated_conjecture,(
% 19.10/2.99    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 19.10/2.99    inference(negated_conjecture,[],[f16])).
% 19.10/2.99  
% 19.10/2.99  fof(f19,plain,(
% 19.10/2.99    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 19.10/2.99    inference(ennf_transformation,[],[f17])).
% 19.10/2.99  
% 19.10/2.99  fof(f20,plain,(
% 19.10/2.99    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 19.10/2.99    introduced(choice_axiom,[])).
% 19.10/2.99  
% 19.10/2.99  fof(f21,plain,(
% 19.10/2.99    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 19.10/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).
% 19.10/2.99  
% 19.10/2.99  fof(f37,plain,(
% 19.10/2.99    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 19.10/2.99    inference(cnf_transformation,[],[f21])).
% 19.10/2.99  
% 19.10/2.99  fof(f41,plain,(
% 19.10/2.99    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 19.10/2.99    inference(definition_unfolding,[],[f37,f31])).
% 19.10/2.99  
% 19.10/2.99  cnf(c_1,plain,
% 19.10/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 19.10/2.99      inference(cnf_transformation,[],[f38]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_9,plain,
% 19.10/2.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 19.10/2.99      inference(cnf_transformation,[],[f39]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_0,plain,
% 19.10/2.99      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 19.10/2.99      inference(cnf_transformation,[],[f22]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_8,plain,
% 19.10/2.99      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 19.10/2.99      inference(cnf_transformation,[],[f30]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_66,plain,
% 19.10/2.99      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_0,c_8]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_310,plain,
% 19.10/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_9,c_66]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_5,plain,
% 19.10/2.99      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 19.10/2.99      inference(cnf_transformation,[],[f27]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_408,plain,
% 19.10/2.99      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_310,c_5]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_4,plain,
% 19.10/2.99      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 19.10/2.99      inference(cnf_transformation,[],[f26]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_411,plain,
% 19.10/2.99      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 19.10/2.99      inference(light_normalisation,[status(thm)],[c_408,c_4]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_420,plain,
% 19.10/2.99      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_1,c_411]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_13,plain,
% 19.10/2.99      ( k2_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
% 19.10/2.99      inference(cnf_transformation,[],[f40]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_374,plain,
% 19.10/2.99      ( k4_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_13,c_8]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_702,plain,
% 19.10/2.99      ( k4_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_0,c_374]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_1332,plain,
% 19.10/2.99      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_5,c_702]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_288,plain,
% 19.10/2.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = X1 ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_1,c_9]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_16213,plain,
% 19.10/2.99      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X1,X0),X0))),k1_xboole_0) = k5_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_1332,c_288]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_16217,plain,
% 19.10/2.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X1,X0),X0))) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X1,X0),X0),k1_xboole_0) ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_1332,c_1]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_10,plain,
% 19.10/2.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 19.10/2.99      inference(cnf_transformation,[],[f33]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_11,plain,
% 19.10/2.99      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 19.10/2.99      inference(cnf_transformation,[],[f34]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_2,plain,
% 19.10/2.99      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 19.10/2.99      inference(cnf_transformation,[],[f24]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_41,plain,
% 19.10/2.99      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_11,c_2]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_223,plain,
% 19.10/2.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_10,c_41]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_699,plain,
% 19.10/2.99      ( k4_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(k1_xboole_0,k5_xboole_0(X1,X0))) = k1_xboole_0 ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_223,c_374]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_43,plain,
% 19.10/2.99      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_733,plain,
% 19.10/2.99      ( k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = k1_xboole_0 ),
% 19.10/2.99      inference(demodulation,[status(thm)],[c_699,c_43]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_72,plain,
% 19.10/2.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_8,c_5]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_76,plain,
% 19.10/2.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 19.10/2.99      inference(demodulation,[status(thm)],[c_72,c_4]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_437,plain,
% 19.10/2.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_0,c_76]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_945,plain,
% 19.10/2.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_437,c_8]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_7,plain,
% 19.10/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 19.10/2.99      inference(cnf_transformation,[],[f29]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_271,plain,
% 19.10/2.99      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_7,c_5]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_11390,plain,
% 19.10/2.99      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X1)) = k2_xboole_0(X0,k1_xboole_0) ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_945,c_271]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_11515,plain,
% 19.10/2.99      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X1)) = X0 ),
% 19.10/2.99      inference(light_normalisation,[status(thm)],[c_11390,c_4]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_128,plain,
% 19.10/2.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_66,c_5]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_129,plain,
% 19.10/2.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 19.10/2.99      inference(demodulation,[status(thm)],[c_128,c_4]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_525,plain,
% 19.10/2.99      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_129,c_0]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_11630,plain,
% 19.10/2.99      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X0) = k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X1)) ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_11515,c_525]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_11661,plain,
% 19.10/2.99      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X0) = X0 ),
% 19.10/2.99      inference(demodulation,[status(thm)],[c_11630,c_11515]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_259,plain,
% 19.10/2.99      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_1,c_7]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_12526,plain,
% 19.10/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X0))),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_11661,c_259]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_6,plain,
% 19.10/2.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 19.10/2.99      inference(cnf_transformation,[],[f28]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_12537,plain,
% 19.10/2.99      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 19.10/2.99      inference(light_normalisation,[status(thm)],[c_12526,c_6,c_66]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_13583,plain,
% 19.10/2.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_12537,c_1]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_13601,plain,
% 19.10/2.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
% 19.10/2.99      inference(light_normalisation,[status(thm)],[c_13583,c_6,c_8]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_13737,plain,
% 19.10/2.99      ( k4_xboole_0(k2_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)),k1_xboole_0) = k5_xboole_0(X0,X1) ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_733,c_13601]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_712,plain,
% 19.10/2.99      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k1_xboole_0 ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_411,c_374]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_1763,plain,
% 19.10/2.99      ( k2_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,k1_xboole_0) ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_712,c_5]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_1766,plain,
% 19.10/2.99      ( k2_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 19.10/2.99      inference(light_normalisation,[status(thm)],[c_1763,c_4]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_2305,plain,
% 19.10/2.99      ( k2_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_1766,c_525]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_2316,plain,
% 19.10/2.99      ( k2_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = X0 ),
% 19.10/2.99      inference(demodulation,[status(thm)],[c_2305,c_1766]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_2777,plain,
% 19.10/2.99      ( k2_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0),k5_xboole_0(X0,X1)) = k5_xboole_0(X0,X1) ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_733,c_2316]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_12,plain,
% 19.10/2.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 19.10/2.99      inference(cnf_transformation,[],[f35]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_40,plain,
% 19.10/2.99      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_11,c_2]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_57,plain,
% 19.10/2.99      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_12,c_40]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_60,plain,
% 19.10/2.99      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 19.10/2.99      inference(demodulation,[status(thm)],[c_57,c_10]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_114,plain,
% 19.10/2.99      ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_60,c_60]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_558,plain,
% 19.10/2.99      ( k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) = k5_xboole_0(X1,X0) ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_223,c_114]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_2811,plain,
% 19.10/2.99      ( k2_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = k5_xboole_0(X1,X0) ),
% 19.10/2.99      inference(light_normalisation,[status(thm)],[c_2777,c_558]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_13825,plain,
% 19.10/2.99      ( k4_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) = k5_xboole_0(X1,X0) ),
% 19.10/2.99      inference(light_normalisation,[status(thm)],[c_13737,c_2811]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_16232,plain,
% 19.10/2.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X1,X0),X0))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 19.10/2.99      inference(demodulation,[status(thm)],[c_16217,c_13825]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_16236,plain,
% 19.10/2.99      ( k2_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0) = k5_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 19.10/2.99      inference(demodulation,[status(thm)],[c_16213,c_16232]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_931,plain,
% 19.10/2.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_5,c_437]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_126,plain,
% 19.10/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_5,c_66]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_488,plain,
% 19.10/2.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_126,c_5]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_491,plain,
% 19.10/2.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 19.10/2.99      inference(demodulation,[status(thm)],[c_488,c_4]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_966,plain,
% 19.10/2.99      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 19.10/2.99      inference(light_normalisation,[status(thm)],[c_931,c_491]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_13527,plain,
% 19.10/2.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_966,c_12537]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_13636,plain,
% 19.10/2.99      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 19.10/2.99      inference(demodulation,[status(thm)],[c_13527,c_13601]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_14451,plain,
% 19.10/2.99      ( k2_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_13636,c_13]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_3,plain,
% 19.10/2.99      ( k2_xboole_0(X0,X0) = X0 ),
% 19.10/2.99      inference(cnf_transformation,[],[f25]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_68,plain,
% 19.10/2.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_3,c_8]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_514,plain,
% 19.10/2.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_0,c_129]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_1037,plain,
% 19.10/2.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_5,c_514]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_1075,plain,
% 19.10/2.99      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 19.10/2.99      inference(demodulation,[status(thm)],[c_1037,c_514]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_2622,plain,
% 19.10/2.99      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_1075,c_0]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_14495,plain,
% 19.10/2.99      ( k2_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 19.10/2.99      inference(light_normalisation,[status(thm)],[c_14451,c_68,c_2622]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_16237,plain,
% 19.10/2.99      ( k5_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 19.10/2.99      inference(light_normalisation,[status(thm)],[c_16236,c_14495]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_107,plain,
% 19.10/2.99      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_2,c_60]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_139,plain,
% 19.10/2.99      ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_107,c_60]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_19139,plain,
% 19.10/2.99      ( k5_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_16237,c_139]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_19856,plain,
% 19.10/2.99      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_420,c_19139]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_406,plain,
% 19.10/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_310,c_1]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_412,plain,
% 19.10/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 19.10/2.99      inference(demodulation,[status(thm)],[c_406,c_4,c_7]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_7554,plain,
% 19.10/2.99      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_1,c_412]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_20027,plain,
% 19.10/2.99      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 19.10/2.99      inference(light_normalisation,[status(thm)],[c_19856,c_7554]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_14,negated_conjecture,
% 19.10/2.99      ( k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
% 19.10/2.99      inference(cnf_transformation,[],[f41]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_32,negated_conjecture,
% 19.10/2.99      ( k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
% 19.10/2.99      inference(theory_normalisation,[status(thm)],[c_14,c_11,c_2]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_90330,plain,
% 19.10/2.99      ( k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k2_xboole_0(sK0,sK1) ),
% 19.10/2.99      inference(demodulation,[status(thm)],[c_20027,c_32]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_13526,plain,
% 19.10/2.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_1075,c_12537]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_13637,plain,
% 19.10/2.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
% 19.10/2.99      inference(demodulation,[status(thm)],[c_13526,c_13636]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_19100,plain,
% 19.10/2.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_13637,c_16237]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_7852,plain,
% 19.10/2.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 19.10/2.99      inference(superposition,[status(thm)],[c_0,c_491]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_19251,plain,
% 19.10/2.99      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 19.10/2.99      inference(light_normalisation,[status(thm)],[c_19100,c_7852]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_90331,plain,
% 19.10/2.99      ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) ),
% 19.10/2.99      inference(demodulation,[status(thm)],[c_90330,c_19251]) ).
% 19.10/2.99  
% 19.10/2.99  cnf(c_90332,plain,
% 19.10/2.99      ( $false ),
% 19.10/2.99      inference(equality_resolution_simp,[status(thm)],[c_90331]) ).
% 19.10/2.99  
% 19.10/2.99  
% 19.10/2.99  % SZS output end CNFRefutation for theBenchmark.p
% 19.10/2.99  
% 19.10/2.99  ------                               Statistics
% 19.10/2.99  
% 19.10/2.99  ------ General
% 19.10/2.99  
% 19.10/2.99  abstr_ref_over_cycles:                  0
% 19.10/2.99  abstr_ref_under_cycles:                 0
% 19.10/2.99  gc_basic_clause_elim:                   0
% 19.10/2.99  forced_gc_time:                         0
% 19.10/2.99  parsing_time:                           0.009
% 19.10/2.99  unif_index_cands_time:                  0.
% 19.10/2.99  unif_index_add_time:                    0.
% 19.10/2.99  orderings_time:                         0.
% 19.10/2.99  out_proof_time:                         0.008
% 19.10/2.99  total_time:                             2.192
% 19.10/2.99  num_of_symbols:                         40
% 19.10/2.99  num_of_terms:                           113183
% 19.10/2.99  
% 19.10/2.99  ------ Preprocessing
% 19.10/2.99  
% 19.10/2.99  num_of_splits:                          0
% 19.10/2.99  num_of_split_atoms:                     3
% 19.10/2.99  num_of_reused_defs:                     10
% 19.10/2.99  num_eq_ax_congr_red:                    0
% 19.10/2.99  num_of_sem_filtered_clauses:            0
% 19.10/2.99  num_of_subtypes:                        0
% 19.10/2.99  monotx_restored_types:                  0
% 19.10/2.99  sat_num_of_epr_types:                   0
% 19.10/2.99  sat_num_of_non_cyclic_types:            0
% 19.10/2.99  sat_guarded_non_collapsed_types:        0
% 19.10/2.99  num_pure_diseq_elim:                    0
% 19.10/2.99  simp_replaced_by:                       0
% 19.10/2.99  res_preprocessed:                       35
% 19.10/2.99  prep_upred:                             0
% 19.10/2.99  prep_unflattend:                        0
% 19.10/2.99  smt_new_axioms:                         0
% 19.10/2.99  pred_elim_cands:                        0
% 19.10/2.99  pred_elim:                              0
% 19.10/2.99  pred_elim_cl:                           0
% 19.10/2.99  pred_elim_cycles:                       0
% 19.10/2.99  merged_defs:                            0
% 19.10/2.99  merged_defs_ncl:                        0
% 19.10/2.99  bin_hyper_res:                          0
% 19.10/2.99  prep_cycles:                            2
% 19.10/2.99  pred_elim_time:                         0.
% 19.10/2.99  splitting_time:                         0.
% 19.10/2.99  sem_filter_time:                        0.
% 19.10/2.99  monotx_time:                            0.
% 19.10/2.99  subtype_inf_time:                       0.
% 19.10/2.99  
% 19.10/2.99  ------ Problem properties
% 19.10/2.99  
% 19.10/2.99  clauses:                                15
% 19.10/2.99  conjectures:                            1
% 19.10/2.99  epr:                                    0
% 19.10/2.99  horn:                                   15
% 19.10/2.99  ground:                                 1
% 19.10/2.99  unary:                                  15
% 19.10/2.99  binary:                                 0
% 19.10/2.99  lits:                                   15
% 19.10/2.99  lits_eq:                                15
% 19.10/2.99  fd_pure:                                0
% 19.10/2.99  fd_pseudo:                              0
% 19.10/2.99  fd_cond:                                0
% 19.10/2.99  fd_pseudo_cond:                         0
% 19.10/2.99  ac_symbols:                             1
% 19.10/2.99  
% 19.10/2.99  ------ Propositional Solver
% 19.10/2.99  
% 19.10/2.99  prop_solver_calls:                      13
% 19.10/2.99  prop_fast_solver_calls:                 86
% 19.10/2.99  smt_solver_calls:                       0
% 19.10/2.99  smt_fast_solver_calls:                  0
% 19.10/2.99  prop_num_of_clauses:                    537
% 19.10/2.99  prop_preprocess_simplified:             663
% 19.10/2.99  prop_fo_subsumed:                       0
% 19.10/2.99  prop_solver_time:                       0.
% 19.10/2.99  smt_solver_time:                        0.
% 19.10/2.99  smt_fast_solver_time:                   0.
% 19.10/2.99  prop_fast_solver_time:                  0.
% 19.10/2.99  prop_unsat_core_time:                   0.
% 19.10/2.99  
% 19.10/2.99  ------ QBF
% 19.10/2.99  
% 19.10/2.99  qbf_q_res:                              0
% 19.10/2.99  qbf_num_tautologies:                    0
% 19.10/2.99  qbf_prep_cycles:                        0
% 19.10/2.99  
% 19.10/2.99  ------ BMC1
% 19.10/2.99  
% 19.10/2.99  bmc1_current_bound:                     -1
% 19.10/2.99  bmc1_last_solved_bound:                 -1
% 19.10/2.99  bmc1_unsat_core_size:                   -1
% 19.10/2.99  bmc1_unsat_core_parents_size:           -1
% 19.10/2.99  bmc1_merge_next_fun:                    0
% 19.10/2.99  bmc1_unsat_core_clauses_time:           0.
% 19.10/2.99  
% 19.10/2.99  ------ Instantiation
% 19.10/2.99  
% 19.10/2.99  inst_num_of_clauses:                    0
% 19.10/2.99  inst_num_in_passive:                    0
% 19.10/2.99  inst_num_in_active:                     0
% 19.10/2.99  inst_num_in_unprocessed:                0
% 19.10/2.99  inst_num_of_loops:                      0
% 19.10/2.99  inst_num_of_learning_restarts:          0
% 19.10/2.99  inst_num_moves_active_passive:          0
% 19.10/2.99  inst_lit_activity:                      0
% 19.10/2.99  inst_lit_activity_moves:                0
% 19.10/2.99  inst_num_tautologies:                   0
% 19.10/2.99  inst_num_prop_implied:                  0
% 19.10/2.99  inst_num_existing_simplified:           0
% 19.10/2.99  inst_num_eq_res_simplified:             0
% 19.10/2.99  inst_num_child_elim:                    0
% 19.10/2.99  inst_num_of_dismatching_blockings:      0
% 19.10/2.99  inst_num_of_non_proper_insts:           0
% 19.10/2.99  inst_num_of_duplicates:                 0
% 19.10/2.99  inst_inst_num_from_inst_to_res:         0
% 19.10/2.99  inst_dismatching_checking_time:         0.
% 19.10/2.99  
% 19.10/2.99  ------ Resolution
% 19.10/2.99  
% 19.10/2.99  res_num_of_clauses:                     0
% 19.10/2.99  res_num_in_passive:                     0
% 19.10/2.99  res_num_in_active:                      0
% 19.10/2.99  res_num_of_loops:                       37
% 19.10/2.99  res_forward_subset_subsumed:            0
% 19.10/2.99  res_backward_subset_subsumed:           0
% 19.10/2.99  res_forward_subsumed:                   0
% 19.10/2.99  res_backward_subsumed:                  0
% 19.10/2.99  res_forward_subsumption_resolution:     0
% 19.10/2.99  res_backward_subsumption_resolution:    0
% 19.10/2.99  res_clause_to_clause_subsumption:       211008
% 19.10/2.99  res_orphan_elimination:                 0
% 19.10/2.99  res_tautology_del:                      0
% 19.10/2.99  res_num_eq_res_simplified:              0
% 19.10/2.99  res_num_sel_changes:                    0
% 19.10/2.99  res_moves_from_active_to_pass:          0
% 19.10/2.99  
% 19.10/2.99  ------ Superposition
% 19.10/2.99  
% 19.10/2.99  sup_time_total:                         0.
% 19.10/2.99  sup_time_generating:                    0.
% 19.10/2.99  sup_time_sim_full:                      0.
% 19.10/2.99  sup_time_sim_immed:                     0.
% 19.10/2.99  
% 19.10/2.99  sup_num_of_clauses:                     8171
% 19.10/2.99  sup_num_in_active:                      256
% 19.10/2.99  sup_num_in_passive:                     7915
% 19.10/2.99  sup_num_of_loops:                       348
% 19.10/2.99  sup_fw_superposition:                   34720
% 19.10/2.99  sup_bw_superposition:                   27124
% 19.10/2.99  sup_immediate_simplified:               26953
% 19.10/2.99  sup_given_eliminated:                   14
% 19.10/2.99  comparisons_done:                       0
% 19.10/2.99  comparisons_avoided:                    0
% 19.10/2.99  
% 19.10/2.99  ------ Simplifications
% 19.10/2.99  
% 19.10/2.99  
% 19.10/2.99  sim_fw_subset_subsumed:                 0
% 19.10/2.99  sim_bw_subset_subsumed:                 0
% 19.10/2.99  sim_fw_subsumed:                        4478
% 19.10/2.99  sim_bw_subsumed:                        92
% 19.10/2.99  sim_fw_subsumption_res:                 0
% 19.10/2.99  sim_bw_subsumption_res:                 0
% 19.10/2.99  sim_tautology_del:                      0
% 19.10/2.99  sim_eq_tautology_del:                   7418
% 19.10/2.99  sim_eq_res_simp:                        0
% 19.10/2.99  sim_fw_demodulated:                     15688
% 19.10/2.99  sim_bw_demodulated:                     506
% 19.10/2.99  sim_light_normalised:                   11733
% 19.10/2.99  sim_joinable_taut:                      156
% 19.10/2.99  sim_joinable_simp:                      0
% 19.10/2.99  sim_ac_normalised:                      0
% 19.10/2.99  sim_smt_subsumption:                    0
% 19.10/2.99  
%------------------------------------------------------------------------------
