%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:57 EST 2020

% Result     : Theorem 20.09s
% Output     : CNFRefutation 20.09s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 468 expanded)
%              Number of clauses        :   76 ( 223 expanded)
%              Number of leaves         :   15 ( 116 expanded)
%              Depth                    :   18
%              Number of atoms          :  111 ( 469 expanded)
%              Number of equality atoms :  110 ( 468 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f12,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f17,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f17])).

fof(f20,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f18])).

fof(f21,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f21])).

fof(f39,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f41,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f39,f25,f25])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f11,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_12,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_10,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_61,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2,c_10])).

cnf(c_179,plain,
    ( k3_xboole_0(X0,k4_xboole_0(X1,k3_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12,c_61])).

cnf(c_11,plain,
    ( k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_67,plain,
    ( k4_xboole_0(X0,k3_xboole_0(X1,X0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_11])).

cnf(c_180,plain,
    ( k3_xboole_0(X0,k4_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_179,c_67])).

cnf(c_5,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_359,plain,
    ( k3_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_180,c_5])).

cnf(c_8,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_75,plain,
    ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_61,c_8])).

cnf(c_76,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_75,c_2])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_84,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_76,c_0])).

cnf(c_370,plain,
    ( k3_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k3_xboole_0(X0,X2) ),
    inference(demodulation,[status(thm)],[c_359,c_84])).

cnf(c_19257,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_370,c_11])).

cnf(c_19313,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
    inference(demodulation,[status(thm)],[c_19257,c_11])).

cnf(c_15,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_43,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_15,c_12])).

cnf(c_44,plain,
    ( k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_0,c_43])).

cnf(c_90868,plain,
    ( k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_19313,c_44])).

cnf(c_13,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_362,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_180,c_11])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_367,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_362,c_9])).

cnf(c_442,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_367,c_367])).

cnf(c_2729,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k3_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_13,c_442])).

cnf(c_2787,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_2729,c_13])).

cnf(c_434,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_11,c_367])).

cnf(c_166,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X1,k4_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_1,c_12])).

cnf(c_15167,plain,
    ( k3_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_434,c_166])).

cnf(c_90869,plain,
    ( k2_xboole_0(k3_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_90868,c_2787,c_15167])).

cnf(c_91329,plain,
    ( k2_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) != k2_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1,c_90869])).

cnf(c_3,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_45,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_3])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_52,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_4])).

cnf(c_119,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_45,c_52])).

cnf(c_958,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_119])).

cnf(c_3356,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_8,c_958])).

cnf(c_3422,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_3356,c_958])).

cnf(c_9777,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_3422,c_0])).

cnf(c_10129,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) = k2_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_13,c_9777])).

cnf(c_294,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) = k2_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_13,c_8])).

cnf(c_9727,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k3_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_13,c_3422])).

cnf(c_71,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_11,c_8])).

cnf(c_47,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_2,c_3])).

cnf(c_202,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_47,c_5])).

cnf(c_219,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_202,c_45])).

cnf(c_2165,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_71,c_71,c_219])).

cnf(c_118,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_3,c_52])).

cnf(c_877,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_118])).

cnf(c_2345,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2165,c_877])).

cnf(c_378,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),X1) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_219])).

cnf(c_59,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_10])).

cnf(c_131,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8,c_59])).

cnf(c_1066,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_378,c_131])).

cnf(c_1086,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1066,c_67])).

cnf(c_1124,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1086,c_8])).

cnf(c_1138,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1124,c_76])).

cnf(c_2401,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2345,c_1138])).

cnf(c_8785,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k3_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_13,c_2401])).

cnf(c_193,plain,
    ( k3_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(X0,k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_45,c_5])).

cnf(c_227,plain,
    ( k3_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = X0 ),
    inference(demodulation,[status(thm)],[c_193,c_4])).

cnf(c_58,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_4,c_45])).

cnf(c_141,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1,c_58])).

cnf(c_1443,plain,
    ( k3_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X1) = k3_xboole_0(X1,k2_xboole_0(k2_xboole_0(X0,X1),X2)) ),
    inference(superposition,[status(thm)],[c_227,c_141])).

cnf(c_1467,plain,
    ( k3_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X1) = X1 ),
    inference(demodulation,[status(thm)],[c_1443,c_227])).

cnf(c_4390,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_4,c_1467])).

cnf(c_8973,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_8785,c_4390])).

cnf(c_9834,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_9727,c_8973])).

cnf(c_10232,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_10129,c_294,c_9834])).

cnf(c_91331,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_91329,c_10232])).

cnf(c_91332,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_91331])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:52:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 20.09/3.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.09/3.00  
% 20.09/3.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 20.09/3.00  
% 20.09/3.00  ------  iProver source info
% 20.09/3.00  
% 20.09/3.00  git: date: 2020-06-30 10:37:57 +0100
% 20.09/3.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 20.09/3.00  git: non_committed_changes: false
% 20.09/3.00  git: last_make_outside_of_git: false
% 20.09/3.00  
% 20.09/3.00  ------ 
% 20.09/3.00  
% 20.09/3.00  ------ Input Options
% 20.09/3.00  
% 20.09/3.00  --out_options                           all
% 20.09/3.00  --tptp_safe_out                         true
% 20.09/3.00  --problem_path                          ""
% 20.09/3.00  --include_path                          ""
% 20.09/3.00  --clausifier                            res/vclausify_rel
% 20.09/3.00  --clausifier_options                    ""
% 20.09/3.00  --stdin                                 false
% 20.09/3.00  --stats_out                             all
% 20.09/3.00  
% 20.09/3.00  ------ General Options
% 20.09/3.00  
% 20.09/3.00  --fof                                   false
% 20.09/3.00  --time_out_real                         305.
% 20.09/3.00  --time_out_virtual                      -1.
% 20.09/3.00  --symbol_type_check                     false
% 20.09/3.00  --clausify_out                          false
% 20.09/3.00  --sig_cnt_out                           false
% 20.09/3.00  --trig_cnt_out                          false
% 20.09/3.00  --trig_cnt_out_tolerance                1.
% 20.09/3.00  --trig_cnt_out_sk_spl                   false
% 20.09/3.00  --abstr_cl_out                          false
% 20.09/3.00  
% 20.09/3.00  ------ Global Options
% 20.09/3.00  
% 20.09/3.00  --schedule                              default
% 20.09/3.00  --add_important_lit                     false
% 20.09/3.00  --prop_solver_per_cl                    1000
% 20.09/3.00  --min_unsat_core                        false
% 20.09/3.00  --soft_assumptions                      false
% 20.09/3.00  --soft_lemma_size                       3
% 20.09/3.00  --prop_impl_unit_size                   0
% 20.09/3.00  --prop_impl_unit                        []
% 20.09/3.00  --share_sel_clauses                     true
% 20.09/3.00  --reset_solvers                         false
% 20.09/3.00  --bc_imp_inh                            [conj_cone]
% 20.09/3.00  --conj_cone_tolerance                   3.
% 20.09/3.00  --extra_neg_conj                        none
% 20.09/3.00  --large_theory_mode                     true
% 20.09/3.00  --prolific_symb_bound                   200
% 20.09/3.00  --lt_threshold                          2000
% 20.09/3.00  --clause_weak_htbl                      true
% 20.09/3.00  --gc_record_bc_elim                     false
% 20.09/3.00  
% 20.09/3.00  ------ Preprocessing Options
% 20.09/3.00  
% 20.09/3.00  --preprocessing_flag                    true
% 20.09/3.00  --time_out_prep_mult                    0.1
% 20.09/3.00  --splitting_mode                        input
% 20.09/3.00  --splitting_grd                         true
% 20.09/3.00  --splitting_cvd                         false
% 20.09/3.00  --splitting_cvd_svl                     false
% 20.09/3.00  --splitting_nvd                         32
% 20.09/3.00  --sub_typing                            true
% 20.09/3.00  --prep_gs_sim                           true
% 20.09/3.00  --prep_unflatten                        true
% 20.09/3.00  --prep_res_sim                          true
% 20.09/3.00  --prep_upred                            true
% 20.09/3.00  --prep_sem_filter                       exhaustive
% 20.09/3.00  --prep_sem_filter_out                   false
% 20.09/3.00  --pred_elim                             true
% 20.09/3.00  --res_sim_input                         true
% 20.09/3.00  --eq_ax_congr_red                       true
% 20.09/3.00  --pure_diseq_elim                       true
% 20.09/3.00  --brand_transform                       false
% 20.09/3.00  --non_eq_to_eq                          false
% 20.09/3.00  --prep_def_merge                        true
% 20.09/3.00  --prep_def_merge_prop_impl              false
% 20.09/3.00  --prep_def_merge_mbd                    true
% 20.09/3.00  --prep_def_merge_tr_red                 false
% 20.09/3.00  --prep_def_merge_tr_cl                  false
% 20.09/3.00  --smt_preprocessing                     true
% 20.09/3.00  --smt_ac_axioms                         fast
% 20.09/3.00  --preprocessed_out                      false
% 20.09/3.00  --preprocessed_stats                    false
% 20.09/3.00  
% 20.09/3.00  ------ Abstraction refinement Options
% 20.09/3.00  
% 20.09/3.00  --abstr_ref                             []
% 20.09/3.00  --abstr_ref_prep                        false
% 20.09/3.00  --abstr_ref_until_sat                   false
% 20.09/3.00  --abstr_ref_sig_restrict                funpre
% 20.09/3.00  --abstr_ref_af_restrict_to_split_sk     false
% 20.09/3.00  --abstr_ref_under                       []
% 20.09/3.00  
% 20.09/3.00  ------ SAT Options
% 20.09/3.00  
% 20.09/3.00  --sat_mode                              false
% 20.09/3.00  --sat_fm_restart_options                ""
% 20.09/3.00  --sat_gr_def                            false
% 20.09/3.00  --sat_epr_types                         true
% 20.09/3.00  --sat_non_cyclic_types                  false
% 20.09/3.00  --sat_finite_models                     false
% 20.09/3.00  --sat_fm_lemmas                         false
% 20.09/3.00  --sat_fm_prep                           false
% 20.09/3.00  --sat_fm_uc_incr                        true
% 20.09/3.00  --sat_out_model                         small
% 20.09/3.00  --sat_out_clauses                       false
% 20.09/3.00  
% 20.09/3.00  ------ QBF Options
% 20.09/3.00  
% 20.09/3.00  --qbf_mode                              false
% 20.09/3.00  --qbf_elim_univ                         false
% 20.09/3.00  --qbf_dom_inst                          none
% 20.09/3.00  --qbf_dom_pre_inst                      false
% 20.09/3.00  --qbf_sk_in                             false
% 20.09/3.00  --qbf_pred_elim                         true
% 20.09/3.00  --qbf_split                             512
% 20.09/3.00  
% 20.09/3.00  ------ BMC1 Options
% 20.09/3.00  
% 20.09/3.00  --bmc1_incremental                      false
% 20.09/3.00  --bmc1_axioms                           reachable_all
% 20.09/3.00  --bmc1_min_bound                        0
% 20.09/3.00  --bmc1_max_bound                        -1
% 20.09/3.00  --bmc1_max_bound_default                -1
% 20.09/3.00  --bmc1_symbol_reachability              true
% 20.09/3.00  --bmc1_property_lemmas                  false
% 20.09/3.00  --bmc1_k_induction                      false
% 20.09/3.00  --bmc1_non_equiv_states                 false
% 20.09/3.00  --bmc1_deadlock                         false
% 20.09/3.00  --bmc1_ucm                              false
% 20.09/3.00  --bmc1_add_unsat_core                   none
% 20.09/3.00  --bmc1_unsat_core_children              false
% 20.09/3.00  --bmc1_unsat_core_extrapolate_axioms    false
% 20.09/3.00  --bmc1_out_stat                         full
% 20.09/3.00  --bmc1_ground_init                      false
% 20.09/3.00  --bmc1_pre_inst_next_state              false
% 20.09/3.00  --bmc1_pre_inst_state                   false
% 20.09/3.00  --bmc1_pre_inst_reach_state             false
% 20.09/3.00  --bmc1_out_unsat_core                   false
% 20.09/3.00  --bmc1_aig_witness_out                  false
% 20.09/3.00  --bmc1_verbose                          false
% 20.09/3.00  --bmc1_dump_clauses_tptp                false
% 20.09/3.00  --bmc1_dump_unsat_core_tptp             false
% 20.09/3.00  --bmc1_dump_file                        -
% 20.09/3.00  --bmc1_ucm_expand_uc_limit              128
% 20.09/3.00  --bmc1_ucm_n_expand_iterations          6
% 20.09/3.00  --bmc1_ucm_extend_mode                  1
% 20.09/3.00  --bmc1_ucm_init_mode                    2
% 20.09/3.00  --bmc1_ucm_cone_mode                    none
% 20.09/3.00  --bmc1_ucm_reduced_relation_type        0
% 20.09/3.00  --bmc1_ucm_relax_model                  4
% 20.09/3.00  --bmc1_ucm_full_tr_after_sat            true
% 20.09/3.00  --bmc1_ucm_expand_neg_assumptions       false
% 20.09/3.00  --bmc1_ucm_layered_model                none
% 20.09/3.00  --bmc1_ucm_max_lemma_size               10
% 20.09/3.00  
% 20.09/3.00  ------ AIG Options
% 20.09/3.00  
% 20.09/3.00  --aig_mode                              false
% 20.09/3.00  
% 20.09/3.00  ------ Instantiation Options
% 20.09/3.00  
% 20.09/3.00  --instantiation_flag                    true
% 20.09/3.00  --inst_sos_flag                         true
% 20.09/3.00  --inst_sos_phase                        true
% 20.09/3.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 20.09/3.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 20.09/3.00  --inst_lit_sel_side                     num_symb
% 20.09/3.00  --inst_solver_per_active                1400
% 20.09/3.00  --inst_solver_calls_frac                1.
% 20.09/3.00  --inst_passive_queue_type               priority_queues
% 20.09/3.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 20.09/3.00  --inst_passive_queues_freq              [25;2]
% 20.09/3.00  --inst_dismatching                      true
% 20.09/3.00  --inst_eager_unprocessed_to_passive     true
% 20.09/3.00  --inst_prop_sim_given                   true
% 20.09/3.00  --inst_prop_sim_new                     false
% 20.09/3.00  --inst_subs_new                         false
% 20.09/3.00  --inst_eq_res_simp                      false
% 20.09/3.00  --inst_subs_given                       false
% 20.09/3.00  --inst_orphan_elimination               true
% 20.09/3.00  --inst_learning_loop_flag               true
% 20.09/3.00  --inst_learning_start                   3000
% 20.09/3.00  --inst_learning_factor                  2
% 20.09/3.00  --inst_start_prop_sim_after_learn       3
% 20.09/3.00  --inst_sel_renew                        solver
% 20.09/3.00  --inst_lit_activity_flag                true
% 20.09/3.00  --inst_restr_to_given                   false
% 20.09/3.00  --inst_activity_threshold               500
% 20.09/3.00  --inst_out_proof                        true
% 20.09/3.00  
% 20.09/3.00  ------ Resolution Options
% 20.09/3.00  
% 20.09/3.00  --resolution_flag                       true
% 20.09/3.00  --res_lit_sel                           adaptive
% 20.09/3.00  --res_lit_sel_side                      none
% 20.09/3.00  --res_ordering                          kbo
% 20.09/3.00  --res_to_prop_solver                    active
% 20.09/3.00  --res_prop_simpl_new                    false
% 20.09/3.00  --res_prop_simpl_given                  true
% 20.09/3.00  --res_passive_queue_type                priority_queues
% 20.09/3.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 20.09/3.00  --res_passive_queues_freq               [15;5]
% 20.09/3.00  --res_forward_subs                      full
% 20.09/3.00  --res_backward_subs                     full
% 20.09/3.00  --res_forward_subs_resolution           true
% 20.09/3.00  --res_backward_subs_resolution          true
% 20.09/3.00  --res_orphan_elimination                true
% 20.09/3.00  --res_time_limit                        2.
% 20.09/3.00  --res_out_proof                         true
% 20.09/3.00  
% 20.09/3.00  ------ Superposition Options
% 20.09/3.00  
% 20.09/3.00  --superposition_flag                    true
% 20.09/3.00  --sup_passive_queue_type                priority_queues
% 20.09/3.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 20.09/3.00  --sup_passive_queues_freq               [8;1;4]
% 20.09/3.00  --demod_completeness_check              fast
% 20.09/3.00  --demod_use_ground                      true
% 20.09/3.00  --sup_to_prop_solver                    passive
% 20.09/3.00  --sup_prop_simpl_new                    true
% 20.09/3.00  --sup_prop_simpl_given                  true
% 20.09/3.00  --sup_fun_splitting                     true
% 20.09/3.00  --sup_smt_interval                      50000
% 20.09/3.00  
% 20.09/3.00  ------ Superposition Simplification Setup
% 20.09/3.00  
% 20.09/3.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 20.09/3.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 20.09/3.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 20.09/3.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 20.09/3.00  --sup_full_triv                         [TrivRules;PropSubs]
% 20.09/3.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 20.09/3.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 20.09/3.00  --sup_immed_triv                        [TrivRules]
% 20.09/3.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 20.09/3.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 20.09/3.00  --sup_immed_bw_main                     []
% 20.09/3.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 20.09/3.00  --sup_input_triv                        [Unflattening;TrivRules]
% 20.09/3.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 20.09/3.00  --sup_input_bw                          []
% 20.09/3.00  
% 20.09/3.00  ------ Combination Options
% 20.09/3.00  
% 20.09/3.00  --comb_res_mult                         3
% 20.09/3.00  --comb_sup_mult                         2
% 20.09/3.00  --comb_inst_mult                        10
% 20.09/3.00  
% 20.09/3.00  ------ Debug Options
% 20.09/3.00  
% 20.09/3.00  --dbg_backtrace                         false
% 20.09/3.00  --dbg_dump_prop_clauses                 false
% 20.09/3.00  --dbg_dump_prop_clauses_file            -
% 20.09/3.00  --dbg_out_stat                          false
% 20.09/3.00  ------ Parsing...
% 20.09/3.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 20.09/3.00  
% 20.09/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 20.09/3.00  
% 20.09/3.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 20.09/3.00  
% 20.09/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 20.09/3.00  ------ Proving...
% 20.09/3.00  ------ Problem Properties 
% 20.09/3.00  
% 20.09/3.00  
% 20.09/3.00  clauses                                 16
% 20.09/3.00  conjectures                             1
% 20.09/3.00  EPR                                     0
% 20.09/3.00  Horn                                    16
% 20.09/3.00  unary                                   16
% 20.09/3.00  binary                                  0
% 20.09/3.00  lits                                    16
% 20.09/3.00  lits eq                                 16
% 20.09/3.00  fd_pure                                 0
% 20.09/3.00  fd_pseudo                               0
% 20.09/3.00  fd_cond                                 0
% 20.09/3.00  fd_pseudo_cond                          0
% 20.09/3.00  AC symbols                              0
% 20.09/3.00  
% 20.09/3.00  ------ Schedule UEQ
% 20.09/3.00  
% 20.09/3.00  ------ pure equality problem: resolution off 
% 20.09/3.00  
% 20.09/3.00  ------ Option_UEQ Time Limit: Unbounded
% 20.09/3.00  
% 20.09/3.00  
% 20.09/3.00  ------ 
% 20.09/3.00  Current options:
% 20.09/3.00  ------ 
% 20.09/3.00  
% 20.09/3.00  ------ Input Options
% 20.09/3.00  
% 20.09/3.00  --out_options                           all
% 20.09/3.00  --tptp_safe_out                         true
% 20.09/3.00  --problem_path                          ""
% 20.09/3.00  --include_path                          ""
% 20.09/3.00  --clausifier                            res/vclausify_rel
% 20.09/3.00  --clausifier_options                    ""
% 20.09/3.00  --stdin                                 false
% 20.09/3.00  --stats_out                             all
% 20.09/3.00  
% 20.09/3.00  ------ General Options
% 20.09/3.00  
% 20.09/3.00  --fof                                   false
% 20.09/3.00  --time_out_real                         305.
% 20.09/3.00  --time_out_virtual                      -1.
% 20.09/3.00  --symbol_type_check                     false
% 20.09/3.00  --clausify_out                          false
% 20.09/3.00  --sig_cnt_out                           false
% 20.09/3.00  --trig_cnt_out                          false
% 20.09/3.00  --trig_cnt_out_tolerance                1.
% 20.09/3.00  --trig_cnt_out_sk_spl                   false
% 20.09/3.00  --abstr_cl_out                          false
% 20.09/3.00  
% 20.09/3.00  ------ Global Options
% 20.09/3.00  
% 20.09/3.00  --schedule                              default
% 20.09/3.00  --add_important_lit                     false
% 20.09/3.00  --prop_solver_per_cl                    1000
% 20.09/3.00  --min_unsat_core                        false
% 20.09/3.00  --soft_assumptions                      false
% 20.09/3.00  --soft_lemma_size                       3
% 20.09/3.00  --prop_impl_unit_size                   0
% 20.09/3.00  --prop_impl_unit                        []
% 20.09/3.00  --share_sel_clauses                     true
% 20.09/3.00  --reset_solvers                         false
% 20.09/3.00  --bc_imp_inh                            [conj_cone]
% 20.09/3.00  --conj_cone_tolerance                   3.
% 20.09/3.00  --extra_neg_conj                        none
% 20.09/3.00  --large_theory_mode                     true
% 20.09/3.00  --prolific_symb_bound                   200
% 20.09/3.00  --lt_threshold                          2000
% 20.09/3.00  --clause_weak_htbl                      true
% 20.09/3.00  --gc_record_bc_elim                     false
% 20.09/3.00  
% 20.09/3.00  ------ Preprocessing Options
% 20.09/3.00  
% 20.09/3.00  --preprocessing_flag                    true
% 20.09/3.00  --time_out_prep_mult                    0.1
% 20.09/3.00  --splitting_mode                        input
% 20.09/3.00  --splitting_grd                         true
% 20.09/3.00  --splitting_cvd                         false
% 20.09/3.00  --splitting_cvd_svl                     false
% 20.09/3.00  --splitting_nvd                         32
% 20.09/3.00  --sub_typing                            true
% 20.09/3.00  --prep_gs_sim                           true
% 20.09/3.00  --prep_unflatten                        true
% 20.09/3.00  --prep_res_sim                          true
% 20.09/3.00  --prep_upred                            true
% 20.09/3.00  --prep_sem_filter                       exhaustive
% 20.09/3.00  --prep_sem_filter_out                   false
% 20.09/3.00  --pred_elim                             true
% 20.09/3.00  --res_sim_input                         true
% 20.09/3.00  --eq_ax_congr_red                       true
% 20.09/3.00  --pure_diseq_elim                       true
% 20.09/3.00  --brand_transform                       false
% 20.09/3.00  --non_eq_to_eq                          false
% 20.09/3.00  --prep_def_merge                        true
% 20.09/3.00  --prep_def_merge_prop_impl              false
% 20.09/3.00  --prep_def_merge_mbd                    true
% 20.09/3.00  --prep_def_merge_tr_red                 false
% 20.09/3.00  --prep_def_merge_tr_cl                  false
% 20.09/3.00  --smt_preprocessing                     true
% 20.09/3.00  --smt_ac_axioms                         fast
% 20.09/3.00  --preprocessed_out                      false
% 20.09/3.00  --preprocessed_stats                    false
% 20.09/3.00  
% 20.09/3.00  ------ Abstraction refinement Options
% 20.09/3.00  
% 20.09/3.00  --abstr_ref                             []
% 20.09/3.00  --abstr_ref_prep                        false
% 20.09/3.00  --abstr_ref_until_sat                   false
% 20.09/3.00  --abstr_ref_sig_restrict                funpre
% 20.09/3.00  --abstr_ref_af_restrict_to_split_sk     false
% 20.09/3.00  --abstr_ref_under                       []
% 20.09/3.00  
% 20.09/3.00  ------ SAT Options
% 20.09/3.00  
% 20.09/3.00  --sat_mode                              false
% 20.09/3.00  --sat_fm_restart_options                ""
% 20.09/3.00  --sat_gr_def                            false
% 20.09/3.00  --sat_epr_types                         true
% 20.09/3.00  --sat_non_cyclic_types                  false
% 20.09/3.00  --sat_finite_models                     false
% 20.09/3.00  --sat_fm_lemmas                         false
% 20.09/3.00  --sat_fm_prep                           false
% 20.09/3.00  --sat_fm_uc_incr                        true
% 20.09/3.00  --sat_out_model                         small
% 20.09/3.00  --sat_out_clauses                       false
% 20.09/3.00  
% 20.09/3.00  ------ QBF Options
% 20.09/3.00  
% 20.09/3.00  --qbf_mode                              false
% 20.09/3.00  --qbf_elim_univ                         false
% 20.09/3.00  --qbf_dom_inst                          none
% 20.09/3.00  --qbf_dom_pre_inst                      false
% 20.09/3.00  --qbf_sk_in                             false
% 20.09/3.00  --qbf_pred_elim                         true
% 20.09/3.00  --qbf_split                             512
% 20.09/3.00  
% 20.09/3.00  ------ BMC1 Options
% 20.09/3.00  
% 20.09/3.00  --bmc1_incremental                      false
% 20.09/3.00  --bmc1_axioms                           reachable_all
% 20.09/3.00  --bmc1_min_bound                        0
% 20.09/3.00  --bmc1_max_bound                        -1
% 20.09/3.00  --bmc1_max_bound_default                -1
% 20.09/3.00  --bmc1_symbol_reachability              true
% 20.09/3.00  --bmc1_property_lemmas                  false
% 20.09/3.00  --bmc1_k_induction                      false
% 20.09/3.00  --bmc1_non_equiv_states                 false
% 20.09/3.00  --bmc1_deadlock                         false
% 20.09/3.00  --bmc1_ucm                              false
% 20.09/3.00  --bmc1_add_unsat_core                   none
% 20.09/3.00  --bmc1_unsat_core_children              false
% 20.09/3.00  --bmc1_unsat_core_extrapolate_axioms    false
% 20.09/3.00  --bmc1_out_stat                         full
% 20.09/3.00  --bmc1_ground_init                      false
% 20.09/3.00  --bmc1_pre_inst_next_state              false
% 20.09/3.00  --bmc1_pre_inst_state                   false
% 20.09/3.00  --bmc1_pre_inst_reach_state             false
% 20.09/3.00  --bmc1_out_unsat_core                   false
% 20.09/3.00  --bmc1_aig_witness_out                  false
% 20.09/3.00  --bmc1_verbose                          false
% 20.09/3.00  --bmc1_dump_clauses_tptp                false
% 20.09/3.00  --bmc1_dump_unsat_core_tptp             false
% 20.09/3.00  --bmc1_dump_file                        -
% 20.09/3.00  --bmc1_ucm_expand_uc_limit              128
% 20.09/3.00  --bmc1_ucm_n_expand_iterations          6
% 20.09/3.00  --bmc1_ucm_extend_mode                  1
% 20.09/3.00  --bmc1_ucm_init_mode                    2
% 20.09/3.00  --bmc1_ucm_cone_mode                    none
% 20.09/3.00  --bmc1_ucm_reduced_relation_type        0
% 20.09/3.00  --bmc1_ucm_relax_model                  4
% 20.09/3.00  --bmc1_ucm_full_tr_after_sat            true
% 20.09/3.00  --bmc1_ucm_expand_neg_assumptions       false
% 20.09/3.00  --bmc1_ucm_layered_model                none
% 20.09/3.00  --bmc1_ucm_max_lemma_size               10
% 20.09/3.00  
% 20.09/3.00  ------ AIG Options
% 20.09/3.00  
% 20.09/3.00  --aig_mode                              false
% 20.09/3.00  
% 20.09/3.00  ------ Instantiation Options
% 20.09/3.00  
% 20.09/3.00  --instantiation_flag                    false
% 20.09/3.00  --inst_sos_flag                         true
% 20.09/3.00  --inst_sos_phase                        true
% 20.09/3.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 20.09/3.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 20.09/3.00  --inst_lit_sel_side                     num_symb
% 20.09/3.00  --inst_solver_per_active                1400
% 20.09/3.00  --inst_solver_calls_frac                1.
% 20.09/3.00  --inst_passive_queue_type               priority_queues
% 20.09/3.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 20.09/3.00  --inst_passive_queues_freq              [25;2]
% 20.09/3.00  --inst_dismatching                      true
% 20.09/3.00  --inst_eager_unprocessed_to_passive     true
% 20.09/3.00  --inst_prop_sim_given                   true
% 20.09/3.00  --inst_prop_sim_new                     false
% 20.09/3.00  --inst_subs_new                         false
% 20.09/3.00  --inst_eq_res_simp                      false
% 20.09/3.00  --inst_subs_given                       false
% 20.09/3.00  --inst_orphan_elimination               true
% 20.09/3.00  --inst_learning_loop_flag               true
% 20.09/3.00  --inst_learning_start                   3000
% 20.09/3.00  --inst_learning_factor                  2
% 20.09/3.00  --inst_start_prop_sim_after_learn       3
% 20.09/3.00  --inst_sel_renew                        solver
% 20.09/3.00  --inst_lit_activity_flag                true
% 20.09/3.00  --inst_restr_to_given                   false
% 20.09/3.00  --inst_activity_threshold               500
% 20.09/3.00  --inst_out_proof                        true
% 20.09/3.00  
% 20.09/3.00  ------ Resolution Options
% 20.09/3.00  
% 20.09/3.00  --resolution_flag                       false
% 20.09/3.00  --res_lit_sel                           adaptive
% 20.09/3.00  --res_lit_sel_side                      none
% 20.09/3.00  --res_ordering                          kbo
% 20.09/3.00  --res_to_prop_solver                    active
% 20.09/3.00  --res_prop_simpl_new                    false
% 20.09/3.00  --res_prop_simpl_given                  true
% 20.09/3.00  --res_passive_queue_type                priority_queues
% 20.09/3.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 20.09/3.00  --res_passive_queues_freq               [15;5]
% 20.09/3.00  --res_forward_subs                      full
% 20.09/3.00  --res_backward_subs                     full
% 20.09/3.00  --res_forward_subs_resolution           true
% 20.09/3.00  --res_backward_subs_resolution          true
% 20.09/3.00  --res_orphan_elimination                true
% 20.09/3.00  --res_time_limit                        2.
% 20.09/3.00  --res_out_proof                         true
% 20.09/3.00  
% 20.09/3.00  ------ Superposition Options
% 20.09/3.00  
% 20.09/3.00  --superposition_flag                    true
% 20.09/3.00  --sup_passive_queue_type                priority_queues
% 20.09/3.00  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 20.09/3.00  --sup_passive_queues_freq               [8;1;4]
% 20.09/3.00  --demod_completeness_check              fast
% 20.09/3.00  --demod_use_ground                      true
% 20.09/3.00  --sup_to_prop_solver                    active
% 20.09/3.00  --sup_prop_simpl_new                    false
% 20.09/3.00  --sup_prop_simpl_given                  false
% 20.09/3.00  --sup_fun_splitting                     true
% 20.09/3.00  --sup_smt_interval                      10000
% 20.09/3.00  
% 20.09/3.00  ------ Superposition Simplification Setup
% 20.09/3.00  
% 20.09/3.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 20.09/3.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 20.09/3.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 20.09/3.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 20.09/3.00  --sup_full_triv                         [TrivRules]
% 20.09/3.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 20.09/3.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 20.09/3.00  --sup_immed_triv                        [TrivRules]
% 20.09/3.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 20.09/3.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 20.09/3.00  --sup_immed_bw_main                     []
% 20.09/3.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 20.09/3.00  --sup_input_triv                        [Unflattening;TrivRules]
% 20.09/3.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 20.09/3.00  --sup_input_bw                          [BwDemod;BwSubsumption]
% 20.09/3.00  
% 20.09/3.00  ------ Combination Options
% 20.09/3.00  
% 20.09/3.00  --comb_res_mult                         1
% 20.09/3.00  --comb_sup_mult                         1
% 20.09/3.00  --comb_inst_mult                        1000000
% 20.09/3.00  
% 20.09/3.00  ------ Debug Options
% 20.09/3.00  
% 20.09/3.00  --dbg_backtrace                         false
% 20.09/3.00  --dbg_dump_prop_clauses                 false
% 20.09/3.00  --dbg_dump_prop_clauses_file            -
% 20.09/3.00  --dbg_out_stat                          false
% 20.09/3.00  
% 20.09/3.00  
% 20.09/3.00  
% 20.09/3.00  
% 20.09/3.00  ------ Proving...
% 20.09/3.00  
% 20.09/3.00  
% 20.09/3.00  % SZS status Theorem for theBenchmark.p
% 20.09/3.00  
% 20.09/3.00   Resolution empty clause
% 20.09/3.00  
% 20.09/3.00  % SZS output start CNFRefutation for theBenchmark.p
% 20.09/3.00  
% 20.09/3.00  fof(f2,axiom,(
% 20.09/3.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 20.09/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 20.09/3.00  
% 20.09/3.00  fof(f24,plain,(
% 20.09/3.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 20.09/3.00    inference(cnf_transformation,[],[f2])).
% 20.09/3.00  
% 20.09/3.00  fof(f14,axiom,(
% 20.09/3.00    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 20.09/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 20.09/3.00  
% 20.09/3.00  fof(f36,plain,(
% 20.09/3.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 20.09/3.00    inference(cnf_transformation,[],[f14])).
% 20.09/3.00  
% 20.09/3.00  fof(f4,axiom,(
% 20.09/3.00    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 20.09/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 20.09/3.00  
% 20.09/3.00  fof(f19,plain,(
% 20.09/3.00    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 20.09/3.00    inference(rectify,[],[f4])).
% 20.09/3.00  
% 20.09/3.00  fof(f26,plain,(
% 20.09/3.00    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 20.09/3.00    inference(cnf_transformation,[],[f19])).
% 20.09/3.00  
% 20.09/3.00  fof(f12,axiom,(
% 20.09/3.00    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 20.09/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 20.09/3.00  
% 20.09/3.00  fof(f34,plain,(
% 20.09/3.00    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 20.09/3.00    inference(cnf_transformation,[],[f12])).
% 20.09/3.00  
% 20.09/3.00  fof(f13,axiom,(
% 20.09/3.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 20.09/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 20.09/3.00  
% 20.09/3.00  fof(f35,plain,(
% 20.09/3.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 20.09/3.00    inference(cnf_transformation,[],[f13])).
% 20.09/3.00  
% 20.09/3.00  fof(f7,axiom,(
% 20.09/3.00    ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2))),
% 20.09/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 20.09/3.00  
% 20.09/3.00  fof(f29,plain,(
% 20.09/3.00    ( ! [X2,X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 20.09/3.00    inference(cnf_transformation,[],[f7])).
% 20.09/3.00  
% 20.09/3.00  fof(f10,axiom,(
% 20.09/3.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 20.09/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 20.09/3.00  
% 20.09/3.00  fof(f32,plain,(
% 20.09/3.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 20.09/3.00    inference(cnf_transformation,[],[f10])).
% 20.09/3.00  
% 20.09/3.00  fof(f1,axiom,(
% 20.09/3.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 20.09/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 20.09/3.00  
% 20.09/3.00  fof(f23,plain,(
% 20.09/3.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 20.09/3.00    inference(cnf_transformation,[],[f1])).
% 20.09/3.00  
% 20.09/3.00  fof(f17,conjecture,(
% 20.09/3.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 20.09/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 20.09/3.00  
% 20.09/3.00  fof(f18,negated_conjecture,(
% 20.09/3.00    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 20.09/3.00    inference(negated_conjecture,[],[f17])).
% 20.09/3.00  
% 20.09/3.00  fof(f20,plain,(
% 20.09/3.00    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 20.09/3.00    inference(ennf_transformation,[],[f18])).
% 20.09/3.00  
% 20.09/3.00  fof(f21,plain,(
% 20.09/3.00    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 20.09/3.00    introduced(choice_axiom,[])).
% 20.09/3.00  
% 20.09/3.00  fof(f22,plain,(
% 20.09/3.00    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 20.09/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f21])).
% 20.09/3.00  
% 20.09/3.00  fof(f39,plain,(
% 20.09/3.00    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 20.09/3.00    inference(cnf_transformation,[],[f22])).
% 20.09/3.00  
% 20.09/3.00  fof(f3,axiom,(
% 20.09/3.00    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 20.09/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 20.09/3.00  
% 20.09/3.00  fof(f25,plain,(
% 20.09/3.00    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 20.09/3.00    inference(cnf_transformation,[],[f3])).
% 20.09/3.00  
% 20.09/3.00  fof(f41,plain,(
% 20.09/3.00    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 20.09/3.00    inference(definition_unfolding,[],[f39,f25,f25])).
% 20.09/3.00  
% 20.09/3.00  fof(f15,axiom,(
% 20.09/3.00    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 20.09/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 20.09/3.00  
% 20.09/3.00  fof(f37,plain,(
% 20.09/3.00    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 20.09/3.00    inference(cnf_transformation,[],[f15])).
% 20.09/3.00  
% 20.09/3.00  fof(f11,axiom,(
% 20.09/3.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 20.09/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 20.09/3.00  
% 20.09/3.00  fof(f33,plain,(
% 20.09/3.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 20.09/3.00    inference(cnf_transformation,[],[f11])).
% 20.09/3.00  
% 20.09/3.00  fof(f5,axiom,(
% 20.09/3.00    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 20.09/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 20.09/3.00  
% 20.09/3.00  fof(f27,plain,(
% 20.09/3.00    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 20.09/3.00    inference(cnf_transformation,[],[f5])).
% 20.09/3.00  
% 20.09/3.00  fof(f6,axiom,(
% 20.09/3.00    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 20.09/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 20.09/3.00  
% 20.09/3.00  fof(f28,plain,(
% 20.09/3.00    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 20.09/3.00    inference(cnf_transformation,[],[f6])).
% 20.09/3.00  
% 20.09/3.00  cnf(c_1,plain,
% 20.09/3.00      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 20.09/3.00      inference(cnf_transformation,[],[f24]) ).
% 20.09/3.00  
% 20.09/3.00  cnf(c_12,plain,
% 20.09/3.00      ( k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 20.09/3.00      inference(cnf_transformation,[],[f36]) ).
% 20.09/3.00  
% 20.09/3.00  cnf(c_2,plain,
% 20.09/3.00      ( k2_xboole_0(X0,X0) = X0 ),
% 20.09/3.00      inference(cnf_transformation,[],[f26]) ).
% 20.09/3.00  
% 20.09/3.00  cnf(c_10,plain,
% 20.09/3.00      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 20.09/3.00      inference(cnf_transformation,[],[f34]) ).
% 20.09/3.00  
% 20.09/3.00  cnf(c_61,plain,
% 20.09/3.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 20.09/3.00      inference(superposition,[status(thm)],[c_2,c_10]) ).
% 20.09/3.00  
% 20.09/3.00  cnf(c_179,plain,
% 20.09/3.00      ( k3_xboole_0(X0,k4_xboole_0(X1,k3_xboole_0(X0,X1))) = k1_xboole_0 ),
% 20.09/3.00      inference(superposition,[status(thm)],[c_12,c_61]) ).
% 20.09/3.00  
% 20.09/3.00  cnf(c_11,plain,
% 20.09/3.00      ( k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
% 20.09/3.00      inference(cnf_transformation,[],[f35]) ).
% 20.09/3.00  
% 20.09/3.00  cnf(c_67,plain,
% 20.09/3.00      ( k4_xboole_0(X0,k3_xboole_0(X1,X0)) = k4_xboole_0(X0,X1) ),
% 20.09/3.00      inference(superposition,[status(thm)],[c_1,c_11]) ).
% 20.09/3.00  
% 20.09/3.00  cnf(c_180,plain,
% 20.09/3.00      ( k3_xboole_0(X0,k4_xboole_0(X1,X0)) = k1_xboole_0 ),
% 20.09/3.00      inference(demodulation,[status(thm)],[c_179,c_67]) ).
% 20.09/3.00  
% 20.09/3.00  cnf(c_5,plain,
% 20.09/3.00      ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 20.09/3.01      inference(cnf_transformation,[],[f29]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_359,plain,
% 20.09/3.01      ( k3_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X2)) ),
% 20.09/3.01      inference(superposition,[status(thm)],[c_180,c_5]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_8,plain,
% 20.09/3.01      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 20.09/3.01      inference(cnf_transformation,[],[f32]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_75,plain,
% 20.09/3.01      ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
% 20.09/3.01      inference(superposition,[status(thm)],[c_61,c_8]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_76,plain,
% 20.09/3.01      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 20.09/3.01      inference(light_normalisation,[status(thm)],[c_75,c_2]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_0,plain,
% 20.09/3.01      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 20.09/3.01      inference(cnf_transformation,[],[f23]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_84,plain,
% 20.09/3.01      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 20.09/3.01      inference(superposition,[status(thm)],[c_76,c_0]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_370,plain,
% 20.09/3.01      ( k3_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k3_xboole_0(X0,X2) ),
% 20.09/3.01      inference(demodulation,[status(thm)],[c_359,c_84]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_19257,plain,
% 20.09/3.01      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,k3_xboole_0(X0,X2)) ),
% 20.09/3.01      inference(superposition,[status(thm)],[c_370,c_11]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_19313,plain,
% 20.09/3.01      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
% 20.09/3.01      inference(demodulation,[status(thm)],[c_19257,c_11]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_15,negated_conjecture,
% 20.09/3.01      ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
% 20.09/3.01      inference(cnf_transformation,[],[f41]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_43,plain,
% 20.09/3.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) != k2_xboole_0(sK0,sK1) ),
% 20.09/3.01      inference(demodulation,[status(thm)],[c_15,c_12]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_44,plain,
% 20.09/3.01      ( k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1))) != k2_xboole_0(sK0,sK1) ),
% 20.09/3.01      inference(demodulation,[status(thm)],[c_0,c_43]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_90868,plain,
% 20.09/3.01      ( k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1))) != k2_xboole_0(sK0,sK1) ),
% 20.09/3.01      inference(demodulation,[status(thm)],[c_19313,c_44]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_13,plain,
% 20.09/3.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
% 20.09/3.01      inference(cnf_transformation,[],[f37]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_362,plain,
% 20.09/3.01      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 20.09/3.01      inference(superposition,[status(thm)],[c_180,c_11]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_9,plain,
% 20.09/3.01      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 20.09/3.01      inference(cnf_transformation,[],[f33]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_367,plain,
% 20.09/3.01      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 20.09/3.01      inference(light_normalisation,[status(thm)],[c_362,c_9]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_442,plain,
% 20.09/3.01      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 20.09/3.01      inference(superposition,[status(thm)],[c_367,c_367]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_2729,plain,
% 20.09/3.01      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k3_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
% 20.09/3.01      inference(superposition,[status(thm)],[c_13,c_442]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_2787,plain,
% 20.09/3.01      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
% 20.09/3.01      inference(light_normalisation,[status(thm)],[c_2729,c_13]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_434,plain,
% 20.09/3.01      ( k4_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 20.09/3.01      inference(superposition,[status(thm)],[c_11,c_367]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_166,plain,
% 20.09/3.01      ( k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X1,k4_xboole_0(X0,X2)) ),
% 20.09/3.01      inference(superposition,[status(thm)],[c_1,c_12]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_15167,plain,
% 20.09/3.01      ( k3_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k3_xboole_0(X1,X0) ),
% 20.09/3.01      inference(superposition,[status(thm)],[c_434,c_166]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_90869,plain,
% 20.09/3.01      ( k2_xboole_0(k3_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) != k2_xboole_0(sK0,sK1) ),
% 20.09/3.01      inference(demodulation,[status(thm)],[c_90868,c_2787,c_15167]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_91329,plain,
% 20.09/3.01      ( k2_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) != k2_xboole_0(sK0,sK1) ),
% 20.09/3.01      inference(superposition,[status(thm)],[c_1,c_90869]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_3,plain,
% 20.09/3.01      ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
% 20.09/3.01      inference(cnf_transformation,[],[f27]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_45,plain,
% 20.09/3.01      ( k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0 ),
% 20.09/3.01      inference(superposition,[status(thm)],[c_0,c_3]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_4,plain,
% 20.09/3.01      ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 20.09/3.01      inference(cnf_transformation,[],[f28]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_52,plain,
% 20.09/3.01      ( k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
% 20.09/3.01      inference(superposition,[status(thm)],[c_1,c_4]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_119,plain,
% 20.09/3.01      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 20.09/3.01      inference(superposition,[status(thm)],[c_45,c_52]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_958,plain,
% 20.09/3.01      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
% 20.09/3.01      inference(superposition,[status(thm)],[c_0,c_119]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_3356,plain,
% 20.09/3.01      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 20.09/3.01      inference(superposition,[status(thm)],[c_8,c_958]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_3422,plain,
% 20.09/3.01      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 20.09/3.01      inference(demodulation,[status(thm)],[c_3356,c_958]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_9777,plain,
% 20.09/3.01      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 20.09/3.01      inference(superposition,[status(thm)],[c_3422,c_0]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_10129,plain,
% 20.09/3.01      ( k2_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) = k2_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
% 20.09/3.01      inference(superposition,[status(thm)],[c_13,c_9777]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_294,plain,
% 20.09/3.01      ( k2_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) = k2_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
% 20.09/3.01      inference(superposition,[status(thm)],[c_13,c_8]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_9727,plain,
% 20.09/3.01      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k3_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
% 20.09/3.01      inference(superposition,[status(thm)],[c_13,c_3422]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_71,plain,
% 20.09/3.01      ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(k3_xboole_0(X0,X1),X0) ),
% 20.09/3.01      inference(superposition,[status(thm)],[c_11,c_8]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_47,plain,
% 20.09/3.01      ( k3_xboole_0(X0,X0) = X0 ),
% 20.09/3.01      inference(superposition,[status(thm)],[c_2,c_3]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_202,plain,
% 20.09/3.01      ( k3_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(k3_xboole_0(X0,X1),X0) ),
% 20.09/3.01      inference(superposition,[status(thm)],[c_47,c_5]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_219,plain,
% 20.09/3.01      ( k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
% 20.09/3.01      inference(light_normalisation,[status(thm)],[c_202,c_45]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_2165,plain,
% 20.09/3.01      ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
% 20.09/3.01      inference(light_normalisation,[status(thm)],[c_71,c_71,c_219]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_118,plain,
% 20.09/3.01      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 20.09/3.01      inference(superposition,[status(thm)],[c_3,c_52]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_877,plain,
% 20.09/3.01      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 20.09/3.01      inference(superposition,[status(thm)],[c_0,c_118]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_2345,plain,
% 20.09/3.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 20.09/3.01      inference(superposition,[status(thm)],[c_2165,c_877]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_378,plain,
% 20.09/3.01      ( k2_xboole_0(k3_xboole_0(X0,X1),X1) = X1 ),
% 20.09/3.01      inference(superposition,[status(thm)],[c_1,c_219]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_59,plain,
% 20.09/3.01      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 20.09/3.01      inference(superposition,[status(thm)],[c_0,c_10]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_131,plain,
% 20.09/3.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 20.09/3.01      inference(superposition,[status(thm)],[c_8,c_59]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_1066,plain,
% 20.09/3.01      ( k4_xboole_0(k4_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = k1_xboole_0 ),
% 20.09/3.01      inference(superposition,[status(thm)],[c_378,c_131]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_1086,plain,
% 20.09/3.01      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 20.09/3.01      inference(light_normalisation,[status(thm)],[c_1066,c_67]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_1124,plain,
% 20.09/3.01      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
% 20.09/3.01      inference(superposition,[status(thm)],[c_1086,c_8]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_1138,plain,
% 20.09/3.01      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 20.09/3.01      inference(light_normalisation,[status(thm)],[c_1124,c_76]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_2401,plain,
% 20.09/3.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0 ),
% 20.09/3.01      inference(light_normalisation,[status(thm)],[c_2345,c_1138]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_8785,plain,
% 20.09/3.01      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k3_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
% 20.09/3.01      inference(superposition,[status(thm)],[c_13,c_2401]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_193,plain,
% 20.09/3.01      ( k3_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(X0,k3_xboole_0(X0,X2)) ),
% 20.09/3.01      inference(superposition,[status(thm)],[c_45,c_5]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_227,plain,
% 20.09/3.01      ( k3_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = X0 ),
% 20.09/3.01      inference(demodulation,[status(thm)],[c_193,c_4]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_58,plain,
% 20.09/3.01      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
% 20.09/3.01      inference(superposition,[status(thm)],[c_4,c_45]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_141,plain,
% 20.09/3.01      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,X0) ),
% 20.09/3.01      inference(superposition,[status(thm)],[c_1,c_58]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_1443,plain,
% 20.09/3.01      ( k3_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X1) = k3_xboole_0(X1,k2_xboole_0(k2_xboole_0(X0,X1),X2)) ),
% 20.09/3.01      inference(superposition,[status(thm)],[c_227,c_141]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_1467,plain,
% 20.09/3.01      ( k3_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X1) = X1 ),
% 20.09/3.01      inference(demodulation,[status(thm)],[c_1443,c_227]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_4390,plain,
% 20.09/3.01      ( k3_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,X2) ),
% 20.09/3.01      inference(superposition,[status(thm)],[c_4,c_1467]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_8973,plain,
% 20.09/3.01      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 20.09/3.01      inference(demodulation,[status(thm)],[c_8785,c_4390]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_9834,plain,
% 20.09/3.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 20.09/3.01      inference(light_normalisation,[status(thm)],[c_9727,c_8973]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_10232,plain,
% 20.09/3.01      ( k2_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
% 20.09/3.01      inference(light_normalisation,[status(thm)],[c_10129,c_294,c_9834]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_91331,plain,
% 20.09/3.01      ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) ),
% 20.09/3.01      inference(demodulation,[status(thm)],[c_91329,c_10232]) ).
% 20.09/3.01  
% 20.09/3.01  cnf(c_91332,plain,
% 20.09/3.01      ( $false ),
% 20.09/3.01      inference(equality_resolution_simp,[status(thm)],[c_91331]) ).
% 20.09/3.01  
% 20.09/3.01  
% 20.09/3.01  % SZS output end CNFRefutation for theBenchmark.p
% 20.09/3.01  
% 20.09/3.01  ------                               Statistics
% 20.09/3.01  
% 20.09/3.01  ------ General
% 20.09/3.01  
% 20.09/3.01  abstr_ref_over_cycles:                  0
% 20.09/3.01  abstr_ref_under_cycles:                 0
% 20.09/3.01  gc_basic_clause_elim:                   0
% 20.09/3.01  forced_gc_time:                         0
% 20.09/3.01  parsing_time:                           0.011
% 20.09/3.01  unif_index_cands_time:                  0.
% 20.09/3.01  unif_index_add_time:                    0.
% 20.09/3.01  orderings_time:                         0.
% 20.09/3.01  out_proof_time:                         0.008
% 20.09/3.01  total_time:                             2.465
% 20.09/3.01  num_of_symbols:                         37
% 20.09/3.01  num_of_terms:                           117717
% 20.09/3.01  
% 20.09/3.01  ------ Preprocessing
% 20.09/3.01  
% 20.09/3.01  num_of_splits:                          0
% 20.09/3.01  num_of_split_atoms:                     0
% 20.09/3.01  num_of_reused_defs:                     0
% 20.09/3.01  num_eq_ax_congr_red:                    0
% 20.09/3.01  num_of_sem_filtered_clauses:            0
% 20.09/3.01  num_of_subtypes:                        0
% 20.09/3.01  monotx_restored_types:                  0
% 20.09/3.01  sat_num_of_epr_types:                   0
% 20.09/3.01  sat_num_of_non_cyclic_types:            0
% 20.09/3.01  sat_guarded_non_collapsed_types:        0
% 20.09/3.01  num_pure_diseq_elim:                    0
% 20.09/3.01  simp_replaced_by:                       0
% 20.09/3.01  res_preprocessed:                       37
% 20.09/3.01  prep_upred:                             0
% 20.09/3.01  prep_unflattend:                        0
% 20.09/3.01  smt_new_axioms:                         0
% 20.09/3.01  pred_elim_cands:                        0
% 20.09/3.01  pred_elim:                              0
% 20.09/3.01  pred_elim_cl:                           0
% 20.09/3.01  pred_elim_cycles:                       0
% 20.09/3.01  merged_defs:                            0
% 20.09/3.01  merged_defs_ncl:                        0
% 20.09/3.01  bin_hyper_res:                          0
% 20.09/3.01  prep_cycles:                            2
% 20.09/3.01  pred_elim_time:                         0.
% 20.09/3.01  splitting_time:                         0.
% 20.09/3.01  sem_filter_time:                        0.
% 20.09/3.01  monotx_time:                            0.
% 20.09/3.01  subtype_inf_time:                       0.
% 20.09/3.01  
% 20.09/3.01  ------ Problem properties
% 20.09/3.01  
% 20.09/3.01  clauses:                                16
% 20.09/3.01  conjectures:                            1
% 20.09/3.01  epr:                                    0
% 20.09/3.01  horn:                                   16
% 20.09/3.01  ground:                                 1
% 20.09/3.01  unary:                                  16
% 20.09/3.01  binary:                                 0
% 20.09/3.01  lits:                                   16
% 20.09/3.01  lits_eq:                                16
% 20.09/3.01  fd_pure:                                0
% 20.09/3.01  fd_pseudo:                              0
% 20.09/3.01  fd_cond:                                0
% 20.09/3.01  fd_pseudo_cond:                         0
% 20.09/3.01  ac_symbols:                             0
% 20.09/3.01  
% 20.09/3.01  ------ Propositional Solver
% 20.09/3.01  
% 20.09/3.01  prop_solver_calls:                      13
% 20.09/3.01  prop_fast_solver_calls:                 90
% 20.09/3.01  smt_solver_calls:                       0
% 20.09/3.01  smt_fast_solver_calls:                  0
% 20.09/3.01  prop_num_of_clauses:                    529
% 20.09/3.01  prop_preprocess_simplified:             667
% 20.09/3.01  prop_fo_subsumed:                       0
% 20.09/3.01  prop_solver_time:                       0.
% 20.09/3.01  smt_solver_time:                        0.
% 20.09/3.01  smt_fast_solver_time:                   0.
% 20.09/3.01  prop_fast_solver_time:                  0.
% 20.09/3.01  prop_unsat_core_time:                   0.
% 20.09/3.01  
% 20.09/3.01  ------ QBF
% 20.09/3.01  
% 20.09/3.01  qbf_q_res:                              0
% 20.09/3.01  qbf_num_tautologies:                    0
% 20.09/3.01  qbf_prep_cycles:                        0
% 20.09/3.01  
% 20.09/3.01  ------ BMC1
% 20.09/3.01  
% 20.09/3.01  bmc1_current_bound:                     -1
% 20.09/3.01  bmc1_last_solved_bound:                 -1
% 20.09/3.01  bmc1_unsat_core_size:                   -1
% 20.09/3.01  bmc1_unsat_core_parents_size:           -1
% 20.09/3.01  bmc1_merge_next_fun:                    0
% 20.09/3.01  bmc1_unsat_core_clauses_time:           0.
% 20.09/3.01  
% 20.09/3.01  ------ Instantiation
% 20.09/3.01  
% 20.09/3.01  inst_num_of_clauses:                    0
% 20.09/3.01  inst_num_in_passive:                    0
% 20.09/3.01  inst_num_in_active:                     0
% 20.09/3.01  inst_num_in_unprocessed:                0
% 20.09/3.01  inst_num_of_loops:                      0
% 20.09/3.01  inst_num_of_learning_restarts:          0
% 20.09/3.01  inst_num_moves_active_passive:          0
% 20.09/3.01  inst_lit_activity:                      0
% 20.09/3.01  inst_lit_activity_moves:                0
% 20.09/3.01  inst_num_tautologies:                   0
% 20.09/3.01  inst_num_prop_implied:                  0
% 20.09/3.01  inst_num_existing_simplified:           0
% 20.09/3.01  inst_num_eq_res_simplified:             0
% 20.09/3.01  inst_num_child_elim:                    0
% 20.09/3.01  inst_num_of_dismatching_blockings:      0
% 20.09/3.01  inst_num_of_non_proper_insts:           0
% 20.09/3.01  inst_num_of_duplicates:                 0
% 20.09/3.01  inst_inst_num_from_inst_to_res:         0
% 20.09/3.01  inst_dismatching_checking_time:         0.
% 20.09/3.01  
% 20.09/3.01  ------ Resolution
% 20.09/3.01  
% 20.09/3.01  res_num_of_clauses:                     0
% 20.09/3.01  res_num_in_passive:                     0
% 20.09/3.01  res_num_in_active:                      0
% 20.09/3.01  res_num_of_loops:                       39
% 20.09/3.01  res_forward_subset_subsumed:            0
% 20.09/3.01  res_backward_subset_subsumed:           0
% 20.09/3.01  res_forward_subsumed:                   0
% 20.09/3.01  res_backward_subsumed:                  0
% 20.09/3.01  res_forward_subsumption_resolution:     0
% 20.09/3.01  res_backward_subsumption_resolution:    0
% 20.09/3.01  res_clause_to_clause_subsumption:       242010
% 20.09/3.01  res_orphan_elimination:                 0
% 20.09/3.01  res_tautology_del:                      0
% 20.09/3.01  res_num_eq_res_simplified:              0
% 20.09/3.01  res_num_sel_changes:                    0
% 20.09/3.01  res_moves_from_active_to_pass:          0
% 20.09/3.01  
% 20.09/3.01  ------ Superposition
% 20.09/3.01  
% 20.09/3.01  sup_time_total:                         0.
% 20.09/3.01  sup_time_generating:                    0.
% 20.09/3.01  sup_time_sim_full:                      0.
% 20.09/3.01  sup_time_sim_immed:                     0.
% 20.09/3.01  
% 20.09/3.01  sup_num_of_clauses:                     8888
% 20.09/3.01  sup_num_in_active:                      315
% 20.09/3.01  sup_num_in_passive:                     8573
% 20.09/3.01  sup_num_of_loops:                       331
% 20.09/3.01  sup_fw_superposition:                   38139
% 20.09/3.01  sup_bw_superposition:                   27989
% 20.09/3.01  sup_immediate_simplified:               25926
% 20.09/3.01  sup_given_eliminated:                   0
% 20.09/3.01  comparisons_done:                       0
% 20.09/3.01  comparisons_avoided:                    0
% 20.09/3.01  
% 20.09/3.01  ------ Simplifications
% 20.09/3.01  
% 20.09/3.01  
% 20.09/3.01  sim_fw_subset_subsumed:                 0
% 20.09/3.01  sim_bw_subset_subsumed:                 0
% 20.09/3.01  sim_fw_subsumed:                        4978
% 20.09/3.01  sim_bw_subsumed:                        53
% 20.09/3.01  sim_fw_subsumption_res:                 0
% 20.09/3.01  sim_bw_subsumption_res:                 0
% 20.09/3.01  sim_tautology_del:                      0
% 20.09/3.01  sim_eq_tautology_del:                   6300
% 20.09/3.01  sim_eq_res_simp:                        0
% 20.09/3.01  sim_fw_demodulated:                     12109
% 20.09/3.01  sim_bw_demodulated:                     92
% 20.09/3.01  sim_light_normalised:                   12787
% 20.09/3.01  sim_joinable_taut:                      0
% 20.09/3.01  sim_joinable_simp:                      0
% 20.09/3.01  sim_ac_normalised:                      0
% 20.09/3.01  sim_smt_subsumption:                    0
% 20.09/3.01  
%------------------------------------------------------------------------------
