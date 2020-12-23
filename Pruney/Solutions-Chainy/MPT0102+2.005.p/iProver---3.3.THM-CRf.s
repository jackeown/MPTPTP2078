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
% DateTime   : Thu Dec  3 11:25:03 EST 2020

% Result     : Theorem 23.28s
% Output     : CNFRefutation 23.28s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 831 expanded)
%              Number of clauses        :   54 ( 298 expanded)
%              Number of leaves         :   16 ( 236 expanded)
%              Depth                    :   18
%              Number of atoms          :   97 ( 832 expanded)
%              Number of equality atoms :   96 ( 831 expanded)
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

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f23,f32,f32])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f36,f24,f32])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f40,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f28,f32])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f27,f32])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f16,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f16])).

fof(f19,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f17])).

fof(f20,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).

fof(f37,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f45,plain,(
    k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(definition_unfolding,[],[f37,f32,f24,f24])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f25,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f35,f32])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_12,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_10,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_32,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k2_xboole_0(X0,X1) ),
    inference(theory_normalisation,[status(thm)],[c_12,c_10,c_0])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_42,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5,c_6])).

cnf(c_7,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_101,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_42,c_7])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_48,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_60,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4,c_48])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_191,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_60,c_8])).

cnf(c_284,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_101,c_191])).

cnf(c_291,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10,c_284])).

cnf(c_2887,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_32,c_291])).

cnf(c_13,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_31,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(theory_normalisation,[status(thm)],[c_13,c_10,c_0])).

cnf(c_103316,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k1_xboole_0) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_2887,c_31])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_159,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2,c_10])).

cnf(c_380,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_159])).

cnf(c_287,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_284])).

cnf(c_895,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_380,c_287])).

cnf(c_85,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_32])).

cnf(c_11,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_33,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_11,c_10,c_0])).

cnf(c_90,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_85,c_33])).

cnf(c_271,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k2_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_7,c_90])).

cnf(c_20298,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X0) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_895,c_271])).

cnf(c_20601,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_20298,c_48])).

cnf(c_97,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_7])).

cnf(c_21265,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X0))),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_20601,c_97])).

cnf(c_21329,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_21265,c_6,c_287])).

cnf(c_22038,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))),X2) ),
    inference(superposition,[status(thm)],[c_21329,c_97])).

cnf(c_22163,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
    inference(light_normalisation,[status(thm)],[c_22038,c_6,c_284])).

cnf(c_295,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_90,c_284])).

cnf(c_519,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10,c_295])).

cnf(c_269,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = k2_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1,c_90])).

cnf(c_138,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_8,c_4])).

cnf(c_283,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_269,c_138])).

cnf(c_26304,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(k2_xboole_0(X0,X1),X2))),k1_xboole_0) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_519,c_283])).

cnf(c_45,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_10,c_0])).

cnf(c_21978,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_45,c_21329])).

cnf(c_46,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_10,c_0])).

cnf(c_22073,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_21329,c_1])).

cnf(c_22143,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_22073,c_6,c_284])).

cnf(c_22413,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(k2_xboole_0(X0,X1),X2)) = X2 ),
    inference(superposition,[status(thm)],[c_46,c_22143])).

cnf(c_26364,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k1_xboole_0) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(light_normalisation,[status(thm)],[c_26304,c_21978,c_22413])).

cnf(c_103317,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_103316,c_22163,c_26364])).

cnf(c_104632,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1,c_103317])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:13:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 23.28/3.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.28/3.49  
% 23.28/3.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.28/3.49  
% 23.28/3.49  ------  iProver source info
% 23.28/3.49  
% 23.28/3.49  git: date: 2020-06-30 10:37:57 +0100
% 23.28/3.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.28/3.49  git: non_committed_changes: false
% 23.28/3.49  git: last_make_outside_of_git: false
% 23.28/3.49  
% 23.28/3.49  ------ 
% 23.28/3.49  
% 23.28/3.49  ------ Input Options
% 23.28/3.49  
% 23.28/3.49  --out_options                           all
% 23.28/3.49  --tptp_safe_out                         true
% 23.28/3.49  --problem_path                          ""
% 23.28/3.49  --include_path                          ""
% 23.28/3.49  --clausifier                            res/vclausify_rel
% 23.28/3.49  --clausifier_options                    --mode clausify
% 23.28/3.49  --stdin                                 false
% 23.28/3.49  --stats_out                             all
% 23.28/3.49  
% 23.28/3.49  ------ General Options
% 23.28/3.49  
% 23.28/3.49  --fof                                   false
% 23.28/3.49  --time_out_real                         305.
% 23.28/3.49  --time_out_virtual                      -1.
% 23.28/3.49  --symbol_type_check                     false
% 23.28/3.49  --clausify_out                          false
% 23.28/3.49  --sig_cnt_out                           false
% 23.28/3.49  --trig_cnt_out                          false
% 23.28/3.49  --trig_cnt_out_tolerance                1.
% 23.28/3.49  --trig_cnt_out_sk_spl                   false
% 23.28/3.49  --abstr_cl_out                          false
% 23.28/3.49  
% 23.28/3.49  ------ Global Options
% 23.28/3.49  
% 23.28/3.49  --schedule                              default
% 23.28/3.49  --add_important_lit                     false
% 23.28/3.49  --prop_solver_per_cl                    1000
% 23.28/3.49  --min_unsat_core                        false
% 23.28/3.49  --soft_assumptions                      false
% 23.28/3.49  --soft_lemma_size                       3
% 23.28/3.49  --prop_impl_unit_size                   0
% 23.28/3.49  --prop_impl_unit                        []
% 23.28/3.49  --share_sel_clauses                     true
% 23.28/3.49  --reset_solvers                         false
% 23.28/3.49  --bc_imp_inh                            [conj_cone]
% 23.28/3.49  --conj_cone_tolerance                   3.
% 23.28/3.49  --extra_neg_conj                        none
% 23.28/3.49  --large_theory_mode                     true
% 23.28/3.49  --prolific_symb_bound                   200
% 23.28/3.49  --lt_threshold                          2000
% 23.28/3.49  --clause_weak_htbl                      true
% 23.28/3.49  --gc_record_bc_elim                     false
% 23.28/3.49  
% 23.28/3.49  ------ Preprocessing Options
% 23.28/3.49  
% 23.28/3.49  --preprocessing_flag                    true
% 23.28/3.49  --time_out_prep_mult                    0.1
% 23.28/3.49  --splitting_mode                        input
% 23.28/3.49  --splitting_grd                         true
% 23.28/3.49  --splitting_cvd                         false
% 23.28/3.49  --splitting_cvd_svl                     false
% 23.28/3.49  --splitting_nvd                         32
% 23.28/3.49  --sub_typing                            true
% 23.28/3.49  --prep_gs_sim                           true
% 23.28/3.49  --prep_unflatten                        true
% 23.28/3.49  --prep_res_sim                          true
% 23.28/3.49  --prep_upred                            true
% 23.28/3.49  --prep_sem_filter                       exhaustive
% 23.28/3.49  --prep_sem_filter_out                   false
% 23.28/3.49  --pred_elim                             true
% 23.28/3.49  --res_sim_input                         true
% 23.28/3.49  --eq_ax_congr_red                       true
% 23.28/3.49  --pure_diseq_elim                       true
% 23.28/3.49  --brand_transform                       false
% 23.28/3.49  --non_eq_to_eq                          false
% 23.28/3.49  --prep_def_merge                        true
% 23.28/3.49  --prep_def_merge_prop_impl              false
% 23.28/3.49  --prep_def_merge_mbd                    true
% 23.28/3.49  --prep_def_merge_tr_red                 false
% 23.28/3.49  --prep_def_merge_tr_cl                  false
% 23.28/3.49  --smt_preprocessing                     true
% 23.28/3.49  --smt_ac_axioms                         fast
% 23.28/3.49  --preprocessed_out                      false
% 23.28/3.49  --preprocessed_stats                    false
% 23.28/3.49  
% 23.28/3.49  ------ Abstraction refinement Options
% 23.28/3.49  
% 23.28/3.49  --abstr_ref                             []
% 23.28/3.49  --abstr_ref_prep                        false
% 23.28/3.49  --abstr_ref_until_sat                   false
% 23.28/3.49  --abstr_ref_sig_restrict                funpre
% 23.28/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.28/3.49  --abstr_ref_under                       []
% 23.28/3.49  
% 23.28/3.49  ------ SAT Options
% 23.28/3.49  
% 23.28/3.49  --sat_mode                              false
% 23.28/3.49  --sat_fm_restart_options                ""
% 23.28/3.49  --sat_gr_def                            false
% 23.28/3.49  --sat_epr_types                         true
% 23.28/3.49  --sat_non_cyclic_types                  false
% 23.28/3.49  --sat_finite_models                     false
% 23.28/3.49  --sat_fm_lemmas                         false
% 23.28/3.49  --sat_fm_prep                           false
% 23.28/3.49  --sat_fm_uc_incr                        true
% 23.28/3.49  --sat_out_model                         small
% 23.28/3.49  --sat_out_clauses                       false
% 23.28/3.49  
% 23.28/3.49  ------ QBF Options
% 23.28/3.49  
% 23.28/3.49  --qbf_mode                              false
% 23.28/3.49  --qbf_elim_univ                         false
% 23.28/3.49  --qbf_dom_inst                          none
% 23.28/3.49  --qbf_dom_pre_inst                      false
% 23.28/3.49  --qbf_sk_in                             false
% 23.28/3.49  --qbf_pred_elim                         true
% 23.28/3.49  --qbf_split                             512
% 23.28/3.49  
% 23.28/3.49  ------ BMC1 Options
% 23.28/3.49  
% 23.28/3.49  --bmc1_incremental                      false
% 23.28/3.49  --bmc1_axioms                           reachable_all
% 23.28/3.49  --bmc1_min_bound                        0
% 23.28/3.49  --bmc1_max_bound                        -1
% 23.28/3.49  --bmc1_max_bound_default                -1
% 23.28/3.49  --bmc1_symbol_reachability              true
% 23.28/3.49  --bmc1_property_lemmas                  false
% 23.28/3.49  --bmc1_k_induction                      false
% 23.28/3.49  --bmc1_non_equiv_states                 false
% 23.28/3.49  --bmc1_deadlock                         false
% 23.28/3.49  --bmc1_ucm                              false
% 23.28/3.49  --bmc1_add_unsat_core                   none
% 23.28/3.49  --bmc1_unsat_core_children              false
% 23.28/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.28/3.49  --bmc1_out_stat                         full
% 23.28/3.49  --bmc1_ground_init                      false
% 23.28/3.49  --bmc1_pre_inst_next_state              false
% 23.28/3.49  --bmc1_pre_inst_state                   false
% 23.28/3.49  --bmc1_pre_inst_reach_state             false
% 23.28/3.49  --bmc1_out_unsat_core                   false
% 23.28/3.49  --bmc1_aig_witness_out                  false
% 23.28/3.49  --bmc1_verbose                          false
% 23.28/3.49  --bmc1_dump_clauses_tptp                false
% 23.28/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.28/3.49  --bmc1_dump_file                        -
% 23.28/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.28/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.28/3.49  --bmc1_ucm_extend_mode                  1
% 23.28/3.49  --bmc1_ucm_init_mode                    2
% 23.28/3.49  --bmc1_ucm_cone_mode                    none
% 23.28/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.28/3.49  --bmc1_ucm_relax_model                  4
% 23.28/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.28/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.28/3.49  --bmc1_ucm_layered_model                none
% 23.28/3.49  --bmc1_ucm_max_lemma_size               10
% 23.28/3.49  
% 23.28/3.49  ------ AIG Options
% 23.28/3.49  
% 23.28/3.49  --aig_mode                              false
% 23.28/3.49  
% 23.28/3.49  ------ Instantiation Options
% 23.28/3.49  
% 23.28/3.49  --instantiation_flag                    true
% 23.28/3.49  --inst_sos_flag                         false
% 23.28/3.49  --inst_sos_phase                        true
% 23.28/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.28/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.28/3.49  --inst_lit_sel_side                     num_symb
% 23.28/3.49  --inst_solver_per_active                1400
% 23.28/3.49  --inst_solver_calls_frac                1.
% 23.28/3.49  --inst_passive_queue_type               priority_queues
% 23.28/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.28/3.49  --inst_passive_queues_freq              [25;2]
% 23.28/3.49  --inst_dismatching                      true
% 23.28/3.49  --inst_eager_unprocessed_to_passive     true
% 23.28/3.49  --inst_prop_sim_given                   true
% 23.28/3.49  --inst_prop_sim_new                     false
% 23.28/3.49  --inst_subs_new                         false
% 23.28/3.49  --inst_eq_res_simp                      false
% 23.28/3.49  --inst_subs_given                       false
% 23.28/3.49  --inst_orphan_elimination               true
% 23.28/3.49  --inst_learning_loop_flag               true
% 23.28/3.49  --inst_learning_start                   3000
% 23.28/3.49  --inst_learning_factor                  2
% 23.28/3.49  --inst_start_prop_sim_after_learn       3
% 23.28/3.49  --inst_sel_renew                        solver
% 23.28/3.49  --inst_lit_activity_flag                true
% 23.28/3.49  --inst_restr_to_given                   false
% 23.28/3.49  --inst_activity_threshold               500
% 23.28/3.49  --inst_out_proof                        true
% 23.28/3.49  
% 23.28/3.49  ------ Resolution Options
% 23.28/3.49  
% 23.28/3.49  --resolution_flag                       true
% 23.28/3.49  --res_lit_sel                           adaptive
% 23.28/3.49  --res_lit_sel_side                      none
% 23.28/3.49  --res_ordering                          kbo
% 23.28/3.49  --res_to_prop_solver                    active
% 23.28/3.49  --res_prop_simpl_new                    false
% 23.28/3.49  --res_prop_simpl_given                  true
% 23.28/3.49  --res_passive_queue_type                priority_queues
% 23.28/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.28/3.49  --res_passive_queues_freq               [15;5]
% 23.28/3.49  --res_forward_subs                      full
% 23.28/3.49  --res_backward_subs                     full
% 23.28/3.49  --res_forward_subs_resolution           true
% 23.28/3.49  --res_backward_subs_resolution          true
% 23.28/3.49  --res_orphan_elimination                true
% 23.28/3.49  --res_time_limit                        2.
% 23.28/3.49  --res_out_proof                         true
% 23.28/3.49  
% 23.28/3.49  ------ Superposition Options
% 23.28/3.49  
% 23.28/3.49  --superposition_flag                    true
% 23.28/3.49  --sup_passive_queue_type                priority_queues
% 23.28/3.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.28/3.49  --sup_passive_queues_freq               [8;1;4]
% 23.28/3.49  --demod_completeness_check              fast
% 23.28/3.49  --demod_use_ground                      true
% 23.28/3.49  --sup_to_prop_solver                    passive
% 23.28/3.49  --sup_prop_simpl_new                    true
% 23.28/3.49  --sup_prop_simpl_given                  true
% 23.28/3.49  --sup_fun_splitting                     false
% 23.28/3.49  --sup_smt_interval                      50000
% 23.28/3.49  
% 23.28/3.49  ------ Superposition Simplification Setup
% 23.28/3.49  
% 23.28/3.49  --sup_indices_passive                   []
% 23.28/3.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.28/3.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.28/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.28/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 23.28/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.28/3.49  --sup_full_bw                           [BwDemod]
% 23.28/3.49  --sup_immed_triv                        [TrivRules]
% 23.28/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.28/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.28/3.49  --sup_immed_bw_main                     []
% 23.28/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.28/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 23.28/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.28/3.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.28/3.49  
% 23.28/3.49  ------ Combination Options
% 23.28/3.49  
% 23.28/3.49  --comb_res_mult                         3
% 23.28/3.49  --comb_sup_mult                         2
% 23.28/3.49  --comb_inst_mult                        10
% 23.28/3.49  
% 23.28/3.49  ------ Debug Options
% 23.28/3.49  
% 23.28/3.49  --dbg_backtrace                         false
% 23.28/3.49  --dbg_dump_prop_clauses                 false
% 23.28/3.49  --dbg_dump_prop_clauses_file            -
% 23.28/3.49  --dbg_out_stat                          false
% 23.28/3.49  ------ Parsing...
% 23.28/3.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.28/3.49  
% 23.28/3.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 23.28/3.49  
% 23.28/3.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.28/3.49  
% 23.28/3.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.28/3.49  ------ Proving...
% 23.28/3.49  ------ Problem Properties 
% 23.28/3.49  
% 23.28/3.49  
% 23.28/3.49  clauses                                 14
% 23.28/3.49  conjectures                             1
% 23.28/3.49  EPR                                     0
% 23.28/3.49  Horn                                    14
% 23.28/3.49  unary                                   14
% 23.28/3.49  binary                                  0
% 23.28/3.49  lits                                    14
% 23.28/3.49  lits eq                                 14
% 23.28/3.49  fd_pure                                 0
% 23.28/3.49  fd_pseudo                               0
% 23.28/3.49  fd_cond                                 0
% 23.28/3.49  fd_pseudo_cond                          0
% 23.28/3.49  AC symbols                              1
% 23.28/3.49  
% 23.28/3.49  ------ Schedule UEQ
% 23.28/3.49  
% 23.28/3.49  ------ pure equality problem: resolution off 
% 23.28/3.49  
% 23.28/3.49  ------ Option_UEQ Time Limit: Unbounded
% 23.28/3.49  
% 23.28/3.49  
% 23.28/3.49  ------ 
% 23.28/3.49  Current options:
% 23.28/3.49  ------ 
% 23.28/3.49  
% 23.28/3.49  ------ Input Options
% 23.28/3.49  
% 23.28/3.49  --out_options                           all
% 23.28/3.49  --tptp_safe_out                         true
% 23.28/3.49  --problem_path                          ""
% 23.28/3.49  --include_path                          ""
% 23.28/3.49  --clausifier                            res/vclausify_rel
% 23.28/3.49  --clausifier_options                    --mode clausify
% 23.28/3.49  --stdin                                 false
% 23.28/3.49  --stats_out                             all
% 23.28/3.49  
% 23.28/3.49  ------ General Options
% 23.28/3.49  
% 23.28/3.49  --fof                                   false
% 23.28/3.49  --time_out_real                         305.
% 23.28/3.49  --time_out_virtual                      -1.
% 23.28/3.49  --symbol_type_check                     false
% 23.28/3.49  --clausify_out                          false
% 23.28/3.49  --sig_cnt_out                           false
% 23.28/3.49  --trig_cnt_out                          false
% 23.28/3.49  --trig_cnt_out_tolerance                1.
% 23.28/3.49  --trig_cnt_out_sk_spl                   false
% 23.28/3.49  --abstr_cl_out                          false
% 23.28/3.49  
% 23.28/3.49  ------ Global Options
% 23.28/3.49  
% 23.28/3.49  --schedule                              default
% 23.28/3.49  --add_important_lit                     false
% 23.28/3.49  --prop_solver_per_cl                    1000
% 23.28/3.49  --min_unsat_core                        false
% 23.28/3.49  --soft_assumptions                      false
% 23.28/3.49  --soft_lemma_size                       3
% 23.28/3.49  --prop_impl_unit_size                   0
% 23.28/3.49  --prop_impl_unit                        []
% 23.28/3.49  --share_sel_clauses                     true
% 23.28/3.49  --reset_solvers                         false
% 23.28/3.49  --bc_imp_inh                            [conj_cone]
% 23.28/3.49  --conj_cone_tolerance                   3.
% 23.28/3.49  --extra_neg_conj                        none
% 23.28/3.49  --large_theory_mode                     true
% 23.28/3.49  --prolific_symb_bound                   200
% 23.28/3.49  --lt_threshold                          2000
% 23.28/3.49  --clause_weak_htbl                      true
% 23.28/3.49  --gc_record_bc_elim                     false
% 23.28/3.49  
% 23.28/3.49  ------ Preprocessing Options
% 23.28/3.49  
% 23.28/3.49  --preprocessing_flag                    true
% 23.28/3.49  --time_out_prep_mult                    0.1
% 23.28/3.49  --splitting_mode                        input
% 23.28/3.49  --splitting_grd                         true
% 23.28/3.49  --splitting_cvd                         false
% 23.28/3.49  --splitting_cvd_svl                     false
% 23.28/3.49  --splitting_nvd                         32
% 23.28/3.49  --sub_typing                            true
% 23.28/3.49  --prep_gs_sim                           true
% 23.28/3.49  --prep_unflatten                        true
% 23.28/3.49  --prep_res_sim                          true
% 23.28/3.49  --prep_upred                            true
% 23.28/3.49  --prep_sem_filter                       exhaustive
% 23.28/3.49  --prep_sem_filter_out                   false
% 23.28/3.49  --pred_elim                             true
% 23.28/3.49  --res_sim_input                         true
% 23.28/3.49  --eq_ax_congr_red                       true
% 23.28/3.49  --pure_diseq_elim                       true
% 23.28/3.49  --brand_transform                       false
% 23.28/3.49  --non_eq_to_eq                          false
% 23.28/3.49  --prep_def_merge                        true
% 23.28/3.49  --prep_def_merge_prop_impl              false
% 23.28/3.49  --prep_def_merge_mbd                    true
% 23.28/3.49  --prep_def_merge_tr_red                 false
% 23.28/3.49  --prep_def_merge_tr_cl                  false
% 23.28/3.49  --smt_preprocessing                     true
% 23.28/3.49  --smt_ac_axioms                         fast
% 23.28/3.49  --preprocessed_out                      false
% 23.28/3.49  --preprocessed_stats                    false
% 23.28/3.49  
% 23.28/3.49  ------ Abstraction refinement Options
% 23.28/3.49  
% 23.28/3.49  --abstr_ref                             []
% 23.28/3.49  --abstr_ref_prep                        false
% 23.28/3.49  --abstr_ref_until_sat                   false
% 23.28/3.49  --abstr_ref_sig_restrict                funpre
% 23.28/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.28/3.49  --abstr_ref_under                       []
% 23.28/3.49  
% 23.28/3.49  ------ SAT Options
% 23.28/3.49  
% 23.28/3.49  --sat_mode                              false
% 23.28/3.49  --sat_fm_restart_options                ""
% 23.28/3.49  --sat_gr_def                            false
% 23.28/3.49  --sat_epr_types                         true
% 23.28/3.49  --sat_non_cyclic_types                  false
% 23.28/3.49  --sat_finite_models                     false
% 23.28/3.49  --sat_fm_lemmas                         false
% 23.28/3.49  --sat_fm_prep                           false
% 23.28/3.49  --sat_fm_uc_incr                        true
% 23.28/3.49  --sat_out_model                         small
% 23.28/3.49  --sat_out_clauses                       false
% 23.28/3.49  
% 23.28/3.49  ------ QBF Options
% 23.28/3.49  
% 23.28/3.49  --qbf_mode                              false
% 23.28/3.49  --qbf_elim_univ                         false
% 23.28/3.49  --qbf_dom_inst                          none
% 23.28/3.49  --qbf_dom_pre_inst                      false
% 23.28/3.49  --qbf_sk_in                             false
% 23.28/3.49  --qbf_pred_elim                         true
% 23.28/3.49  --qbf_split                             512
% 23.28/3.49  
% 23.28/3.49  ------ BMC1 Options
% 23.28/3.49  
% 23.28/3.49  --bmc1_incremental                      false
% 23.28/3.49  --bmc1_axioms                           reachable_all
% 23.28/3.49  --bmc1_min_bound                        0
% 23.28/3.49  --bmc1_max_bound                        -1
% 23.28/3.49  --bmc1_max_bound_default                -1
% 23.28/3.49  --bmc1_symbol_reachability              true
% 23.28/3.49  --bmc1_property_lemmas                  false
% 23.28/3.49  --bmc1_k_induction                      false
% 23.28/3.49  --bmc1_non_equiv_states                 false
% 23.28/3.49  --bmc1_deadlock                         false
% 23.28/3.49  --bmc1_ucm                              false
% 23.28/3.49  --bmc1_add_unsat_core                   none
% 23.28/3.49  --bmc1_unsat_core_children              false
% 23.28/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.28/3.49  --bmc1_out_stat                         full
% 23.28/3.49  --bmc1_ground_init                      false
% 23.28/3.49  --bmc1_pre_inst_next_state              false
% 23.28/3.49  --bmc1_pre_inst_state                   false
% 23.28/3.49  --bmc1_pre_inst_reach_state             false
% 23.28/3.49  --bmc1_out_unsat_core                   false
% 23.28/3.49  --bmc1_aig_witness_out                  false
% 23.28/3.49  --bmc1_verbose                          false
% 23.28/3.49  --bmc1_dump_clauses_tptp                false
% 23.28/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.28/3.49  --bmc1_dump_file                        -
% 23.28/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.28/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.28/3.49  --bmc1_ucm_extend_mode                  1
% 23.28/3.49  --bmc1_ucm_init_mode                    2
% 23.28/3.49  --bmc1_ucm_cone_mode                    none
% 23.28/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.28/3.49  --bmc1_ucm_relax_model                  4
% 23.28/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.28/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.28/3.49  --bmc1_ucm_layered_model                none
% 23.28/3.49  --bmc1_ucm_max_lemma_size               10
% 23.28/3.49  
% 23.28/3.49  ------ AIG Options
% 23.28/3.49  
% 23.28/3.49  --aig_mode                              false
% 23.28/3.49  
% 23.28/3.49  ------ Instantiation Options
% 23.28/3.49  
% 23.28/3.49  --instantiation_flag                    false
% 23.28/3.49  --inst_sos_flag                         false
% 23.28/3.49  --inst_sos_phase                        true
% 23.28/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.28/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.28/3.49  --inst_lit_sel_side                     num_symb
% 23.28/3.49  --inst_solver_per_active                1400
% 23.28/3.49  --inst_solver_calls_frac                1.
% 23.28/3.49  --inst_passive_queue_type               priority_queues
% 23.28/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.28/3.49  --inst_passive_queues_freq              [25;2]
% 23.28/3.49  --inst_dismatching                      true
% 23.28/3.49  --inst_eager_unprocessed_to_passive     true
% 23.28/3.49  --inst_prop_sim_given                   true
% 23.28/3.49  --inst_prop_sim_new                     false
% 23.28/3.49  --inst_subs_new                         false
% 23.28/3.49  --inst_eq_res_simp                      false
% 23.28/3.49  --inst_subs_given                       false
% 23.28/3.49  --inst_orphan_elimination               true
% 23.28/3.49  --inst_learning_loop_flag               true
% 23.28/3.49  --inst_learning_start                   3000
% 23.28/3.49  --inst_learning_factor                  2
% 23.28/3.49  --inst_start_prop_sim_after_learn       3
% 23.28/3.49  --inst_sel_renew                        solver
% 23.28/3.49  --inst_lit_activity_flag                true
% 23.28/3.49  --inst_restr_to_given                   false
% 23.28/3.49  --inst_activity_threshold               500
% 23.28/3.49  --inst_out_proof                        true
% 23.28/3.49  
% 23.28/3.49  ------ Resolution Options
% 23.28/3.49  
% 23.28/3.49  --resolution_flag                       false
% 23.28/3.49  --res_lit_sel                           adaptive
% 23.28/3.49  --res_lit_sel_side                      none
% 23.28/3.49  --res_ordering                          kbo
% 23.28/3.49  --res_to_prop_solver                    active
% 23.28/3.49  --res_prop_simpl_new                    false
% 23.28/3.49  --res_prop_simpl_given                  true
% 23.28/3.49  --res_passive_queue_type                priority_queues
% 23.28/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.28/3.49  --res_passive_queues_freq               [15;5]
% 23.28/3.49  --res_forward_subs                      full
% 23.28/3.49  --res_backward_subs                     full
% 23.28/3.49  --res_forward_subs_resolution           true
% 23.28/3.49  --res_backward_subs_resolution          true
% 23.28/3.49  --res_orphan_elimination                true
% 23.28/3.49  --res_time_limit                        2.
% 23.28/3.49  --res_out_proof                         true
% 23.28/3.49  
% 23.28/3.49  ------ Superposition Options
% 23.28/3.49  
% 23.28/3.49  --superposition_flag                    true
% 23.28/3.49  --sup_passive_queue_type                priority_queues
% 23.28/3.49  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.28/3.49  --sup_passive_queues_freq               [8;1;4]
% 23.28/3.49  --demod_completeness_check              fast
% 23.28/3.49  --demod_use_ground                      true
% 23.28/3.49  --sup_to_prop_solver                    active
% 23.28/3.49  --sup_prop_simpl_new                    false
% 23.28/3.49  --sup_prop_simpl_given                  false
% 23.28/3.49  --sup_fun_splitting                     true
% 23.28/3.49  --sup_smt_interval                      10000
% 23.28/3.49  
% 23.28/3.49  ------ Superposition Simplification Setup
% 23.28/3.49  
% 23.28/3.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.28/3.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.28/3.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.28/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.28/3.49  --sup_full_triv                         [TrivRules]
% 23.28/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.28/3.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.28/3.49  --sup_immed_triv                        [TrivRules]
% 23.28/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.28/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.28/3.49  --sup_immed_bw_main                     []
% 23.28/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.28/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 23.28/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.28/3.49  --sup_input_bw                          [BwDemod;BwSubsumption]
% 23.28/3.49  
% 23.28/3.49  ------ Combination Options
% 23.28/3.49  
% 23.28/3.49  --comb_res_mult                         1
% 23.28/3.49  --comb_sup_mult                         1
% 23.28/3.49  --comb_inst_mult                        1000000
% 23.28/3.49  
% 23.28/3.49  ------ Debug Options
% 23.28/3.49  
% 23.28/3.49  --dbg_backtrace                         false
% 23.28/3.49  --dbg_dump_prop_clauses                 false
% 23.28/3.49  --dbg_dump_prop_clauses_file            -
% 23.28/3.49  --dbg_out_stat                          false
% 23.28/3.49  
% 23.28/3.49  
% 23.28/3.49  
% 23.28/3.49  
% 23.28/3.49  ------ Proving...
% 23.28/3.49  
% 23.28/3.49  
% 23.28/3.49  % SZS status Theorem for theBenchmark.p
% 23.28/3.49  
% 23.28/3.49   Resolution empty clause
% 23.28/3.49  
% 23.28/3.49  % SZS output start CNFRefutation for theBenchmark.p
% 23.28/3.49  
% 23.28/3.49  fof(f2,axiom,(
% 23.28/3.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 23.28/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.28/3.49  
% 23.28/3.49  fof(f23,plain,(
% 23.28/3.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 23.28/3.49    inference(cnf_transformation,[],[f2])).
% 23.28/3.49  
% 23.28/3.49  fof(f11,axiom,(
% 23.28/3.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 23.28/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.28/3.49  
% 23.28/3.49  fof(f32,plain,(
% 23.28/3.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 23.28/3.49    inference(cnf_transformation,[],[f11])).
% 23.28/3.49  
% 23.28/3.49  fof(f38,plain,(
% 23.28/3.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 23.28/3.49    inference(definition_unfolding,[],[f23,f32,f32])).
% 23.28/3.49  
% 23.28/3.49  fof(f15,axiom,(
% 23.28/3.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 23.28/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.28/3.49  
% 23.28/3.49  fof(f36,plain,(
% 23.28/3.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 23.28/3.49    inference(cnf_transformation,[],[f15])).
% 23.28/3.49  
% 23.28/3.49  fof(f3,axiom,(
% 23.28/3.49    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 23.28/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.28/3.49  
% 23.28/3.49  fof(f24,plain,(
% 23.28/3.49    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 23.28/3.49    inference(cnf_transformation,[],[f3])).
% 23.28/3.49  
% 23.28/3.49  fof(f44,plain,(
% 23.28/3.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 23.28/3.49    inference(definition_unfolding,[],[f36,f24,f32])).
% 23.28/3.49  
% 23.28/3.49  fof(f13,axiom,(
% 23.28/3.49    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 23.28/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.28/3.49  
% 23.28/3.49  fof(f34,plain,(
% 23.28/3.49    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 23.28/3.49    inference(cnf_transformation,[],[f13])).
% 23.28/3.49  
% 23.28/3.49  fof(f1,axiom,(
% 23.28/3.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 23.28/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.28/3.49  
% 23.28/3.49  fof(f22,plain,(
% 23.28/3.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 23.28/3.49    inference(cnf_transformation,[],[f1])).
% 23.28/3.49  
% 23.28/3.49  fof(f7,axiom,(
% 23.28/3.49    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 23.28/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.28/3.49  
% 23.28/3.49  fof(f28,plain,(
% 23.28/3.49    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 23.28/3.49    inference(cnf_transformation,[],[f7])).
% 23.28/3.49  
% 23.28/3.49  fof(f40,plain,(
% 23.28/3.49    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 23.28/3.49    inference(definition_unfolding,[],[f28,f32])).
% 23.28/3.49  
% 23.28/3.49  fof(f8,axiom,(
% 23.28/3.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 23.28/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.28/3.49  
% 23.28/3.49  fof(f29,plain,(
% 23.28/3.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 23.28/3.49    inference(cnf_transformation,[],[f8])).
% 23.28/3.49  
% 23.28/3.49  fof(f9,axiom,(
% 23.28/3.49    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 23.28/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.28/3.49  
% 23.28/3.49  fof(f30,plain,(
% 23.28/3.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 23.28/3.49    inference(cnf_transformation,[],[f9])).
% 23.28/3.49  
% 23.28/3.49  fof(f6,axiom,(
% 23.28/3.49    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 23.28/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.28/3.49  
% 23.28/3.49  fof(f27,plain,(
% 23.28/3.49    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 23.28/3.49    inference(cnf_transformation,[],[f6])).
% 23.28/3.49  
% 23.28/3.49  fof(f39,plain,(
% 23.28/3.49    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 23.28/3.49    inference(definition_unfolding,[],[f27,f32])).
% 23.28/3.49  
% 23.28/3.49  fof(f5,axiom,(
% 23.28/3.49    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 23.28/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.28/3.49  
% 23.28/3.49  fof(f26,plain,(
% 23.28/3.49    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 23.28/3.49    inference(cnf_transformation,[],[f5])).
% 23.28/3.49  
% 23.28/3.49  fof(f10,axiom,(
% 23.28/3.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 23.28/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.28/3.49  
% 23.28/3.49  fof(f31,plain,(
% 23.28/3.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 23.28/3.49    inference(cnf_transformation,[],[f10])).
% 23.28/3.49  
% 23.28/3.49  fof(f41,plain,(
% 23.28/3.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 23.28/3.49    inference(definition_unfolding,[],[f31,f32])).
% 23.28/3.49  
% 23.28/3.49  fof(f16,conjecture,(
% 23.28/3.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 23.28/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.28/3.49  
% 23.28/3.49  fof(f17,negated_conjecture,(
% 23.28/3.49    ~! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 23.28/3.49    inference(negated_conjecture,[],[f16])).
% 23.28/3.49  
% 23.28/3.49  fof(f19,plain,(
% 23.28/3.49    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 23.28/3.49    inference(ennf_transformation,[],[f17])).
% 23.28/3.49  
% 23.28/3.49  fof(f20,plain,(
% 23.28/3.49    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 23.28/3.49    introduced(choice_axiom,[])).
% 23.28/3.49  
% 23.28/3.49  fof(f21,plain,(
% 23.28/3.49    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 23.28/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).
% 23.28/3.49  
% 23.28/3.49  fof(f37,plain,(
% 23.28/3.49    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 23.28/3.49    inference(cnf_transformation,[],[f21])).
% 23.28/3.49  
% 23.28/3.49  fof(f45,plain,(
% 23.28/3.49    k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 23.28/3.49    inference(definition_unfolding,[],[f37,f32,f24,f24])).
% 23.28/3.49  
% 23.28/3.49  fof(f4,axiom,(
% 23.28/3.49    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 23.28/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.28/3.49  
% 23.28/3.49  fof(f18,plain,(
% 23.28/3.49    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 23.28/3.49    inference(rectify,[],[f4])).
% 23.28/3.49  
% 23.28/3.49  fof(f25,plain,(
% 23.28/3.49    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 23.28/3.49    inference(cnf_transformation,[],[f18])).
% 23.28/3.49  
% 23.28/3.49  fof(f14,axiom,(
% 23.28/3.49    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 23.28/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.28/3.49  
% 23.28/3.49  fof(f35,plain,(
% 23.28/3.49    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 23.28/3.49    inference(cnf_transformation,[],[f14])).
% 23.28/3.49  
% 23.28/3.49  fof(f43,plain,(
% 23.28/3.49    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 23.28/3.49    inference(definition_unfolding,[],[f35,f32])).
% 23.28/3.49  
% 23.28/3.49  cnf(c_1,plain,
% 23.28/3.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 23.28/3.49      inference(cnf_transformation,[],[f38]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_12,plain,
% 23.28/3.49      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
% 23.28/3.49      inference(cnf_transformation,[],[f44]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_10,plain,
% 23.28/3.49      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 23.28/3.49      inference(cnf_transformation,[],[f34]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_0,plain,
% 23.28/3.49      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 23.28/3.49      inference(cnf_transformation,[],[f22]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_32,plain,
% 23.28/3.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k2_xboole_0(X0,X1) ),
% 23.28/3.49      inference(theory_normalisation,[status(thm)],[c_12,c_10,c_0]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_5,plain,
% 23.28/3.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 23.28/3.49      inference(cnf_transformation,[],[f40]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_6,plain,
% 23.28/3.49      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 23.28/3.49      inference(cnf_transformation,[],[f29]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_42,plain,
% 23.28/3.49      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 23.28/3.49      inference(light_normalisation,[status(thm)],[c_5,c_6]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_7,plain,
% 23.28/3.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 23.28/3.49      inference(cnf_transformation,[],[f30]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_101,plain,
% 23.28/3.49      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
% 23.28/3.49      inference(superposition,[status(thm)],[c_42,c_7]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_4,plain,
% 23.28/3.49      ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 23.28/3.49      inference(cnf_transformation,[],[f39]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_3,plain,
% 23.28/3.49      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 23.28/3.49      inference(cnf_transformation,[],[f26]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_48,plain,
% 23.28/3.49      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 23.28/3.49      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_60,plain,
% 23.28/3.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 23.28/3.49      inference(superposition,[status(thm)],[c_4,c_48]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_8,plain,
% 23.28/3.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 23.28/3.49      inference(cnf_transformation,[],[f41]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_191,plain,
% 23.28/3.49      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 23.28/3.49      inference(superposition,[status(thm)],[c_60,c_8]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_284,plain,
% 23.28/3.49      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 23.28/3.49      inference(demodulation,[status(thm)],[c_101,c_191]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_291,plain,
% 23.28/3.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
% 23.28/3.49      inference(superposition,[status(thm)],[c_10,c_284]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_2887,plain,
% 23.28/3.49      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 23.28/3.49      inference(superposition,[status(thm)],[c_32,c_291]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_13,negated_conjecture,
% 23.28/3.49      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 23.28/3.49      inference(cnf_transformation,[],[f45]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_31,negated_conjecture,
% 23.28/3.49      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 23.28/3.49      inference(theory_normalisation,[status(thm)],[c_13,c_10,c_0]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_103316,plain,
% 23.28/3.49      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k1_xboole_0) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 23.28/3.49      inference(demodulation,[status(thm)],[c_2887,c_31]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_2,plain,
% 23.28/3.49      ( k2_xboole_0(X0,X0) = X0 ),
% 23.28/3.49      inference(cnf_transformation,[],[f25]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_159,plain,
% 23.28/3.49      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 23.28/3.49      inference(superposition,[status(thm)],[c_2,c_10]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_380,plain,
% 23.28/3.49      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 23.28/3.49      inference(superposition,[status(thm)],[c_0,c_159]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_287,plain,
% 23.28/3.49      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 23.28/3.49      inference(superposition,[status(thm)],[c_0,c_284]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_895,plain,
% 23.28/3.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 23.28/3.49      inference(superposition,[status(thm)],[c_380,c_287]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_85,plain,
% 23.28/3.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k2_xboole_0(X0,X1) ),
% 23.28/3.49      inference(superposition,[status(thm)],[c_1,c_32]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_11,plain,
% 23.28/3.49      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 23.28/3.49      inference(cnf_transformation,[],[f43]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_33,plain,
% 23.28/3.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 23.28/3.49      inference(theory_normalisation,[status(thm)],[c_11,c_10,c_0]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_90,plain,
% 23.28/3.49      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 23.28/3.49      inference(demodulation,[status(thm)],[c_85,c_33]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_271,plain,
% 23.28/3.49      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k2_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 23.28/3.49      inference(superposition,[status(thm)],[c_7,c_90]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_20298,plain,
% 23.28/3.49      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X0) = k2_xboole_0(k1_xboole_0,X0) ),
% 23.28/3.49      inference(superposition,[status(thm)],[c_895,c_271]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_20601,plain,
% 23.28/3.49      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X0) = X0 ),
% 23.28/3.49      inference(light_normalisation,[status(thm)],[c_20298,c_48]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_97,plain,
% 23.28/3.49      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 23.28/3.49      inference(superposition,[status(thm)],[c_1,c_7]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_21265,plain,
% 23.28/3.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X0))),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 23.28/3.49      inference(superposition,[status(thm)],[c_20601,c_97]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_21329,plain,
% 23.28/3.49      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 23.28/3.49      inference(light_normalisation,[status(thm)],[c_21265,c_6,c_287]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_22038,plain,
% 23.28/3.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))),X2) ),
% 23.28/3.49      inference(superposition,[status(thm)],[c_21329,c_97]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_22163,plain,
% 23.28/3.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
% 23.28/3.49      inference(light_normalisation,[status(thm)],[c_22038,c_6,c_284]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_295,plain,
% 23.28/3.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 23.28/3.49      inference(superposition,[status(thm)],[c_90,c_284]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_519,plain,
% 23.28/3.49      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
% 23.28/3.49      inference(superposition,[status(thm)],[c_10,c_295]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_269,plain,
% 23.28/3.49      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = k2_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 23.28/3.49      inference(superposition,[status(thm)],[c_1,c_90]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_138,plain,
% 23.28/3.49      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 23.28/3.49      inference(superposition,[status(thm)],[c_8,c_4]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_283,plain,
% 23.28/3.49      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = X1 ),
% 23.28/3.49      inference(demodulation,[status(thm)],[c_269,c_138]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_26304,plain,
% 23.28/3.49      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(k2_xboole_0(X0,X1),X2))),k1_xboole_0) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 23.28/3.49      inference(superposition,[status(thm)],[c_519,c_283]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_45,plain,
% 23.28/3.49      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 23.28/3.49      inference(superposition,[status(thm)],[c_10,c_0]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_21978,plain,
% 23.28/3.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 23.28/3.49      inference(superposition,[status(thm)],[c_45,c_21329]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_46,plain,
% 23.28/3.49      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
% 23.28/3.49      inference(superposition,[status(thm)],[c_10,c_0]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_22073,plain,
% 23.28/3.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
% 23.28/3.49      inference(superposition,[status(thm)],[c_21329,c_1]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_22143,plain,
% 23.28/3.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
% 23.28/3.49      inference(light_normalisation,[status(thm)],[c_22073,c_6,c_284]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_22413,plain,
% 23.28/3.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(k2_xboole_0(X0,X1),X2)) = X2 ),
% 23.28/3.49      inference(superposition,[status(thm)],[c_46,c_22143]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_26364,plain,
% 23.28/3.49      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k1_xboole_0) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 23.28/3.49      inference(light_normalisation,[status(thm)],[c_26304,c_21978,c_22413]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_103317,plain,
% 23.28/3.49      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 23.28/3.49      inference(demodulation,[status(thm)],[c_103316,c_22163,c_26364]) ).
% 23.28/3.49  
% 23.28/3.49  cnf(c_104632,plain,
% 23.28/3.49      ( $false ),
% 23.28/3.49      inference(superposition,[status(thm)],[c_1,c_103317]) ).
% 23.28/3.49  
% 23.28/3.49  
% 23.28/3.49  % SZS output end CNFRefutation for theBenchmark.p
% 23.28/3.49  
% 23.28/3.49  ------                               Statistics
% 23.28/3.49  
% 23.28/3.49  ------ General
% 23.28/3.49  
% 23.28/3.49  abstr_ref_over_cycles:                  0
% 23.28/3.49  abstr_ref_under_cycles:                 0
% 23.28/3.49  gc_basic_clause_elim:                   0
% 23.28/3.49  forced_gc_time:                         0
% 23.28/3.49  parsing_time:                           0.006
% 23.28/3.49  unif_index_cands_time:                  0.
% 23.28/3.49  unif_index_add_time:                    0.
% 23.28/3.49  orderings_time:                         0.
% 23.28/3.49  out_proof_time:                         0.007
% 23.28/3.49  total_time:                             2.727
% 23.28/3.49  num_of_symbols:                         41
% 23.28/3.49  num_of_terms:                           148891
% 23.28/3.49  
% 23.28/3.49  ------ Preprocessing
% 23.28/3.49  
% 23.28/3.49  num_of_splits:                          0
% 23.28/3.49  num_of_split_atoms:                     5
% 23.28/3.49  num_of_reused_defs:                     3
% 23.28/3.49  num_eq_ax_congr_red:                    0
% 23.28/3.49  num_of_sem_filtered_clauses:            0
% 23.28/3.49  num_of_subtypes:                        0
% 23.28/3.49  monotx_restored_types:                  0
% 23.28/3.49  sat_num_of_epr_types:                   0
% 23.28/3.49  sat_num_of_non_cyclic_types:            0
% 23.28/3.49  sat_guarded_non_collapsed_types:        0
% 23.28/3.49  num_pure_diseq_elim:                    0
% 23.28/3.49  simp_replaced_by:                       0
% 23.28/3.49  res_preprocessed:                       32
% 23.28/3.49  prep_upred:                             0
% 23.28/3.49  prep_unflattend:                        0
% 23.28/3.49  smt_new_axioms:                         0
% 23.28/3.49  pred_elim_cands:                        0
% 23.28/3.49  pred_elim:                              0
% 23.28/3.49  pred_elim_cl:                           0
% 23.28/3.49  pred_elim_cycles:                       0
% 23.28/3.49  merged_defs:                            0
% 23.28/3.49  merged_defs_ncl:                        0
% 23.28/3.49  bin_hyper_res:                          0
% 23.28/3.49  prep_cycles:                            2
% 23.28/3.49  pred_elim_time:                         0.
% 23.28/3.49  splitting_time:                         0.
% 23.28/3.49  sem_filter_time:                        0.
% 23.28/3.49  monotx_time:                            0.
% 23.28/3.49  subtype_inf_time:                       0.
% 23.28/3.49  
% 23.28/3.49  ------ Problem properties
% 23.28/3.49  
% 23.28/3.49  clauses:                                14
% 23.28/3.49  conjectures:                            1
% 23.28/3.49  epr:                                    0
% 23.28/3.49  horn:                                   14
% 23.28/3.49  ground:                                 1
% 23.28/3.49  unary:                                  14
% 23.28/3.49  binary:                                 0
% 23.28/3.49  lits:                                   14
% 23.28/3.49  lits_eq:                                14
% 23.28/3.49  fd_pure:                                0
% 23.28/3.49  fd_pseudo:                              0
% 23.28/3.49  fd_cond:                                0
% 23.28/3.49  fd_pseudo_cond:                         0
% 23.28/3.49  ac_symbols:                             1
% 23.28/3.49  
% 23.28/3.49  ------ Propositional Solver
% 23.28/3.49  
% 23.28/3.49  prop_solver_calls:                      13
% 23.28/3.49  prop_fast_solver_calls:                 76
% 23.28/3.49  smt_solver_calls:                       0
% 23.28/3.49  smt_fast_solver_calls:                  0
% 23.28/3.49  prop_num_of_clauses:                    429
% 23.28/3.49  prop_preprocess_simplified:             572
% 23.28/3.49  prop_fo_subsumed:                       0
% 23.28/3.49  prop_solver_time:                       0.
% 23.28/3.49  smt_solver_time:                        0.
% 23.28/3.49  smt_fast_solver_time:                   0.
% 23.28/3.49  prop_fast_solver_time:                  0.
% 23.28/3.49  prop_unsat_core_time:                   0.
% 23.28/3.49  
% 23.28/3.49  ------ QBF
% 23.28/3.49  
% 23.28/3.49  qbf_q_res:                              0
% 23.28/3.49  qbf_num_tautologies:                    0
% 23.28/3.49  qbf_prep_cycles:                        0
% 23.28/3.49  
% 23.28/3.49  ------ BMC1
% 23.28/3.49  
% 23.28/3.49  bmc1_current_bound:                     -1
% 23.28/3.49  bmc1_last_solved_bound:                 -1
% 23.28/3.49  bmc1_unsat_core_size:                   -1
% 23.28/3.49  bmc1_unsat_core_parents_size:           -1
% 23.28/3.49  bmc1_merge_next_fun:                    0
% 23.28/3.49  bmc1_unsat_core_clauses_time:           0.
% 23.28/3.49  
% 23.28/3.49  ------ Instantiation
% 23.28/3.49  
% 23.28/3.49  inst_num_of_clauses:                    0
% 23.28/3.49  inst_num_in_passive:                    0
% 23.28/3.49  inst_num_in_active:                     0
% 23.28/3.49  inst_num_in_unprocessed:                0
% 23.28/3.49  inst_num_of_loops:                      0
% 23.28/3.49  inst_num_of_learning_restarts:          0
% 23.28/3.49  inst_num_moves_active_passive:          0
% 23.28/3.49  inst_lit_activity:                      0
% 23.28/3.49  inst_lit_activity_moves:                0
% 23.28/3.49  inst_num_tautologies:                   0
% 23.28/3.49  inst_num_prop_implied:                  0
% 23.28/3.49  inst_num_existing_simplified:           0
% 23.28/3.49  inst_num_eq_res_simplified:             0
% 23.28/3.49  inst_num_child_elim:                    0
% 23.28/3.49  inst_num_of_dismatching_blockings:      0
% 23.28/3.49  inst_num_of_non_proper_insts:           0
% 23.28/3.49  inst_num_of_duplicates:                 0
% 23.28/3.49  inst_inst_num_from_inst_to_res:         0
% 23.28/3.49  inst_dismatching_checking_time:         0.
% 23.28/3.49  
% 23.28/3.49  ------ Resolution
% 23.28/3.49  
% 23.28/3.49  res_num_of_clauses:                     0
% 23.28/3.49  res_num_in_passive:                     0
% 23.28/3.49  res_num_in_active:                      0
% 23.28/3.49  res_num_of_loops:                       34
% 23.28/3.49  res_forward_subset_subsumed:            0
% 23.28/3.49  res_backward_subset_subsumed:           0
% 23.28/3.49  res_forward_subsumed:                   0
% 23.28/3.49  res_backward_subsumed:                  0
% 23.28/3.49  res_forward_subsumption_resolution:     0
% 23.28/3.49  res_backward_subsumption_resolution:    0
% 23.28/3.49  res_clause_to_clause_subsumption:       353600
% 23.28/3.49  res_orphan_elimination:                 0
% 23.28/3.49  res_tautology_del:                      0
% 23.28/3.49  res_num_eq_res_simplified:              0
% 23.28/3.49  res_num_sel_changes:                    0
% 23.28/3.49  res_moves_from_active_to_pass:          0
% 23.28/3.49  
% 23.28/3.49  ------ Superposition
% 23.28/3.49  
% 23.28/3.49  sup_time_total:                         0.
% 23.28/3.49  sup_time_generating:                    0.
% 23.28/3.49  sup_time_sim_full:                      0.
% 23.28/3.49  sup_time_sim_immed:                     0.
% 23.28/3.49  
% 23.28/3.49  sup_num_of_clauses:                     7310
% 23.28/3.49  sup_num_in_active:                      233
% 23.28/3.49  sup_num_in_passive:                     7077
% 23.28/3.49  sup_num_of_loops:                       270
% 23.28/3.49  sup_fw_superposition:                   36032
% 23.28/3.49  sup_bw_superposition:                   28842
% 23.28/3.49  sup_immediate_simplified:               35240
% 23.28/3.49  sup_given_eliminated:                   9
% 23.28/3.49  comparisons_done:                       0
% 23.28/3.49  comparisons_avoided:                    0
% 23.28/3.49  
% 23.28/3.49  ------ Simplifications
% 23.28/3.49  
% 23.28/3.49  
% 23.28/3.49  sim_fw_subset_subsumed:                 0
% 23.28/3.49  sim_bw_subset_subsumed:                 0
% 23.28/3.49  sim_fw_subsumed:                        3229
% 23.28/3.49  sim_bw_subsumed:                        76
% 23.28/3.49  sim_fw_subsumption_res:                 0
% 23.28/3.49  sim_bw_subsumption_res:                 0
% 23.28/3.49  sim_tautology_del:                      0
% 23.28/3.49  sim_eq_tautology_del:                   8743
% 23.28/3.49  sim_eq_res_simp:                        0
% 23.28/3.49  sim_fw_demodulated:                     26275
% 23.28/3.49  sim_bw_demodulated:                     119
% 23.28/3.49  sim_light_normalised:                   12735
% 23.28/3.49  sim_joinable_taut:                      1159
% 23.28/3.49  sim_joinable_simp:                      0
% 23.28/3.49  sim_ac_normalised:                      0
% 23.28/3.49  sim_smt_subsumption:                    0
% 23.28/3.49  
%------------------------------------------------------------------------------
