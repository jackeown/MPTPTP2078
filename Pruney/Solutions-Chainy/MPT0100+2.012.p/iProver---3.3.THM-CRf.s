%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:56 EST 2020

% Result     : Theorem 6.16s
% Output     : CNFRefutation 6.16s
% Verified   : 
% Statistics : Number of formulae       :  186 (40912 expanded)
%              Number of clauses        :  156 (17981 expanded)
%              Number of leaves         :   12 (10715 expanded)
%              Depth                    :   29
%              Number of atoms          :  187 (40913 expanded)
%              Number of equality atoms :  186 (40912 expanded)
%              Maximal formula depth    :    5 (   1 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f18,f23])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f25,f23])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f11,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f13,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f14,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f26,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f30,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f26,f17,f23])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_5,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_27,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1,c_3])).

cnf(c_67,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_27])).

cnf(c_68,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_67,c_2])).

cnf(c_174,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2,c_68])).

cnf(c_358,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_174,c_5])).

cnf(c_7,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_103,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_27,c_7])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_30,plain,
    ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_27,c_2])).

cnf(c_32,plain,
    ( k2_xboole_0(X0,X0) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_0,c_30])).

cnf(c_4,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_47,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X0),X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_32,c_4])).

cnf(c_111,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_103,c_3,c_27,c_47])).

cnf(c_6,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_79,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X0),X0) = X0 ),
    inference(superposition,[status(thm)],[c_3,c_6])).

cnf(c_88,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_79,c_27])).

cnf(c_112,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_111,c_88])).

cnf(c_361,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_358,c_5,c_112])).

cnf(c_66,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_5,c_5])).

cnf(c_69,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_66,c_5])).

cnf(c_2731,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,k2_xboole_0(X0,X2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_361,c_69])).

cnf(c_179,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_68,c_2])).

cnf(c_51,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4,c_3])).

cnf(c_54,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_51,c_3])).

cnf(c_189,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_179,c_54])).

cnf(c_420,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_189])).

cnf(c_668,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_2,c_420])).

cnf(c_708,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_668,c_420])).

cnf(c_10238,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_2731,c_708])).

cnf(c_172,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_68])).

cnf(c_202,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_172,c_5])).

cnf(c_204,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_202,c_69,c_112])).

cnf(c_445,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X0,X2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_204])).

cnf(c_44,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_4])).

cnf(c_216,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_44,c_2])).

cnf(c_226,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_216,c_2])).

cnf(c_550,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_189,c_226])).

cnf(c_52,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_4,c_2])).

cnf(c_53,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_52,c_2])).

cnf(c_560,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_226,c_53])).

cnf(c_564,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_560,c_420])).

cnf(c_570,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_550,c_564])).

cnf(c_979,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_2,c_570])).

cnf(c_175,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_68])).

cnf(c_242,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_175,c_2])).

cnf(c_254,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_242,c_54])).

cnf(c_286,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_44,c_254])).

cnf(c_1031,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_979,c_286])).

cnf(c_1819,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_445,c_1031])).

cnf(c_953,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_445,c_2])).

cnf(c_269,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_53,c_68])).

cnf(c_835,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_269,c_2])).

cnf(c_425,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_53,c_189])).

cnf(c_434,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_189,c_0])).

cnf(c_441,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_425,c_434])).

cnf(c_853,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_835,c_441])).

cnf(c_970,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k2_xboole_0(k2_xboole_0(X1,X2),X0) ),
    inference(demodulation,[status(thm)],[c_953,c_853])).

cnf(c_1878,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(k2_xboole_0(X1,X2),X0) ),
    inference(light_normalisation,[status(thm)],[c_1819,c_970])).

cnf(c_220,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k4_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_44,c_5])).

cnf(c_221,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_220,c_5])).

cnf(c_2922,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_286])).

cnf(c_9112,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_221,c_2922])).

cnf(c_247,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_175,c_5])).

cnf(c_249,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_247,c_5,c_112])).

cnf(c_602,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_249,c_2])).

cnf(c_617,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_602,c_54])).

cnf(c_9140,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(X1,k2_xboole_0(X0,X3))) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_221,c_617])).

cnf(c_9118,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_221,c_708])).

cnf(c_9172,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(k2_xboole_0(X0,X2),X1) ),
    inference(demodulation,[status(thm)],[c_9118,c_1031])).

cnf(c_9177,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X2),X1) ),
    inference(demodulation,[status(thm)],[c_9112,c_9140,c_9172])).

cnf(c_46,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_2,c_4])).

cnf(c_1639,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_46,c_708])).

cnf(c_1672,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_708,c_0])).

cnf(c_1715,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_1639,c_708,c_1672])).

cnf(c_9178,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_9177,c_1715])).

cnf(c_589,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_249])).

cnf(c_2421,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X3,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_69,c_589])).

cnf(c_10014,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X2,X3)),k1_xboole_0) = k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X2,X3)) ),
    inference(superposition,[status(thm)],[c_2421,c_286])).

cnf(c_10029,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X2,X3)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_2421,c_1031])).

cnf(c_183,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_68,c_5])).

cnf(c_185,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_183,c_69,c_112])).

cnf(c_385,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_185])).

cnf(c_2420,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_69,c_385])).

cnf(c_65,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_5,c_2])).

cnf(c_9858,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X2,X3)) = k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2420,c_65])).

cnf(c_9867,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X2,X3)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_9858,c_853,c_9178])).

cnf(c_10073,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(light_normalisation,[status(thm)],[c_10029,c_1878,c_9867])).

cnf(c_10086,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(k2_xboole_0(X3,X1),k1_xboole_0)) = k2_xboole_0(X1,k2_xboole_0(X3,k2_xboole_0(X0,k4_xboole_0(X1,X2)))) ),
    inference(demodulation,[status(thm)],[c_10014,c_10073])).

cnf(c_10025,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X3,X0))),k1_xboole_0) = k2_xboole_0(k2_xboole_0(X2,k2_xboole_0(X3,X0)),k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2421,c_2922])).

cnf(c_10030,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X3,X0))) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X2,k2_xboole_0(X3,X0))) ),
    inference(superposition,[status(thm)],[c_2421,c_708])).

cnf(c_10072,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X3,X0))) = k2_xboole_0(X0,k2_xboole_0(X3,X2)) ),
    inference(demodulation,[status(thm)],[c_10030,c_1878,c_9178])).

cnf(c_10075,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X0,X3)))) = k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X0,k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_10025,c_10072,c_10073])).

cnf(c_10076,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X0,X3)))) = k2_xboole_0(X2,k2_xboole_0(X1,k2_xboole_0(X0,k1_xboole_0))) ),
    inference(demodulation,[status(thm)],[c_10075,c_10073])).

cnf(c_10077,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X0,X3)))) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_10076,c_54])).

cnf(c_10087,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X0,k2_xboole_0(X3,k1_xboole_0)))) = k2_xboole_0(X2,k2_xboole_0(X3,X0)) ),
    inference(demodulation,[status(thm)],[c_10086,c_10073,c_10077])).

cnf(c_10088,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X0,X3))) = k2_xboole_0(X2,k2_xboole_0(X3,X0)) ),
    inference(demodulation,[status(thm)],[c_10087,c_54])).

cnf(c_10281,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(demodulation,[status(thm)],[c_10238,c_1878,c_9178,c_10088])).

cnf(c_8,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_29,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_0,c_8])).

cnf(c_19650,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_10281,c_29])).

cnf(c_1652,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_589,c_708])).

cnf(c_1702,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
    inference(demodulation,[status(thm)],[c_1652,c_88])).

cnf(c_7891,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1702])).

cnf(c_203,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_172,c_5])).

cnf(c_488,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X0),X0)) ),
    inference(superposition,[status(thm)],[c_4,c_46])).

cnf(c_537,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(X0,X1),X1)) ),
    inference(light_normalisation,[status(thm)],[c_488,c_434])).

cnf(c_538,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_537,c_4])).

cnf(c_15049,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)),k4_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)))) = k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2))),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_203,c_538])).

cnf(c_261,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_6,c_53])).

cnf(c_84,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_276,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_261,c_84])).

cnf(c_61,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_4,c_5])).

cnf(c_71,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_61,c_5])).

cnf(c_4065,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),X1)) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) ),
    inference(superposition,[status(thm)],[c_276,c_71])).

cnf(c_4172,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_4065,c_276])).

cnf(c_10900,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X3)) = k2_xboole_0(X3,k2_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_4172,c_7891])).

cnf(c_611,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X2),X3)) = k4_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[status(thm)],[c_249,c_5])).

cnf(c_613,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X2),X3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_611,c_5,c_112])).

cnf(c_2877,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X2),X3)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(X0,X2),X3)) ),
    inference(superposition,[status(thm)],[c_613,c_708])).

cnf(c_1640,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_172,c_708])).

cnf(c_689,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_420,c_0])).

cnf(c_1714,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_1640,c_689])).

cnf(c_2907,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X2),X3)) = k2_xboole_0(X3,k2_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_2877,c_1714])).

cnf(c_10233,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,k2_xboole_0(X0,X2))),k1_xboole_0) = k2_xboole_0(k2_xboole_0(X1,k2_xboole_0(X0,X2)),k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2731,c_2922])).

cnf(c_10237,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,X0)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_2731,c_1031])).

cnf(c_10282,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X1,X2),X0) ),
    inference(light_normalisation,[status(thm)],[c_10237,c_1878])).

cnf(c_2414,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X0,X3)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_69,c_445])).

cnf(c_8595,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,X3)) = k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2414,c_65])).

cnf(c_8601,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,X3)) = k2_xboole_0(k2_xboole_0(X1,X2),X0) ),
    inference(demodulation,[status(thm)],[c_8595,c_853])).

cnf(c_10283,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,X0)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_10282,c_8601,c_9178])).

cnf(c_10285,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,k2_xboole_0(X0,X2))),k1_xboole_0) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_10233,c_10283])).

cnf(c_9821,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))),X3) = k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2420,c_2])).

cnf(c_9833,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))),X3) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3)))) ),
    inference(superposition,[status(thm)],[c_2420,c_1031])).

cnf(c_9881,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))),X3) = k2_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_9833,c_1878,c_9178])).

cnf(c_9882,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))),X3) = k2_xboole_0(X3,k2_xboole_0(X2,k2_xboole_0(X1,X0))) ),
    inference(demodulation,[status(thm)],[c_9881,c_9178])).

cnf(c_9888,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))),k1_xboole_0) = k2_xboole_0(X3,k2_xboole_0(X2,k2_xboole_0(X1,X0))) ),
    inference(demodulation,[status(thm)],[c_9821,c_9882])).

cnf(c_10286,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_10285,c_853,c_9888,c_10088])).

cnf(c_10974,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X3) = k2_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_10900,c_2907,c_7891,c_10286])).

cnf(c_2837,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X0,X3))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_689,c_613])).

cnf(c_80,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_4,c_6])).

cnf(c_6107,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_80,c_80,c_538])).

cnf(c_10532,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X0,X3))) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X2,k2_xboole_0(X0,X3)),k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2837,c_6107])).

cnf(c_10604,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0),k1_xboole_0) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(light_normalisation,[status(thm)],[c_10532,c_10088])).

cnf(c_10605,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
    inference(demodulation,[status(thm)],[c_10604,c_3,c_853,c_1031])).

cnf(c_4043,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k1_xboole_0,X2)) = k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(k1_xboole_0,X2)) ),
    inference(superposition,[status(thm)],[c_853,c_71])).

cnf(c_60,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_3,c_5])).

cnf(c_4199,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X2) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(demodulation,[status(thm)],[c_4043,c_60])).

cnf(c_13062,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_4199,c_3])).

cnf(c_13217,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_10605,c_13062])).

cnf(c_15232,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_15049,c_203,c_10077,c_10974,c_13217])).

cnf(c_19651,plain,
    ( k2_xboole_0(sK1,sK0) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_19650,c_1031,c_7891,c_15232])).

cnf(c_20205,plain,
    ( $false ),
    inference(theory_normalisation,[status(thm)],[c_19651])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n004.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 11:26:08 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 6.16/1.47  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.16/1.47  
% 6.16/1.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.16/1.47  
% 6.16/1.47  ------  iProver source info
% 6.16/1.47  
% 6.16/1.47  git: date: 2020-06-30 10:37:57 +0100
% 6.16/1.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.16/1.47  git: non_committed_changes: false
% 6.16/1.47  git: last_make_outside_of_git: false
% 6.16/1.47  
% 6.16/1.47  ------ 
% 6.16/1.47  
% 6.16/1.47  ------ Input Options
% 6.16/1.47  
% 6.16/1.47  --out_options                           all
% 6.16/1.47  --tptp_safe_out                         true
% 6.16/1.47  --problem_path                          ""
% 6.16/1.47  --include_path                          ""
% 6.16/1.47  --clausifier                            res/vclausify_rel
% 6.16/1.47  --clausifier_options                    --mode clausify
% 6.16/1.47  --stdin                                 false
% 6.16/1.47  --stats_out                             all
% 6.16/1.47  
% 6.16/1.47  ------ General Options
% 6.16/1.47  
% 6.16/1.47  --fof                                   false
% 6.16/1.47  --time_out_real                         305.
% 6.16/1.47  --time_out_virtual                      -1.
% 6.16/1.47  --symbol_type_check                     false
% 6.16/1.47  --clausify_out                          false
% 6.16/1.47  --sig_cnt_out                           false
% 6.16/1.47  --trig_cnt_out                          false
% 6.16/1.47  --trig_cnt_out_tolerance                1.
% 6.16/1.47  --trig_cnt_out_sk_spl                   false
% 6.16/1.47  --abstr_cl_out                          false
% 6.16/1.47  
% 6.16/1.47  ------ Global Options
% 6.16/1.47  
% 6.16/1.47  --schedule                              default
% 6.16/1.47  --add_important_lit                     false
% 6.16/1.47  --prop_solver_per_cl                    1000
% 6.16/1.47  --min_unsat_core                        false
% 6.16/1.47  --soft_assumptions                      false
% 6.16/1.47  --soft_lemma_size                       3
% 6.16/1.47  --prop_impl_unit_size                   0
% 6.16/1.47  --prop_impl_unit                        []
% 6.16/1.47  --share_sel_clauses                     true
% 6.16/1.47  --reset_solvers                         false
% 6.16/1.47  --bc_imp_inh                            [conj_cone]
% 6.16/1.47  --conj_cone_tolerance                   3.
% 6.16/1.47  --extra_neg_conj                        none
% 6.16/1.47  --large_theory_mode                     true
% 6.16/1.47  --prolific_symb_bound                   200
% 6.16/1.47  --lt_threshold                          2000
% 6.16/1.47  --clause_weak_htbl                      true
% 6.16/1.47  --gc_record_bc_elim                     false
% 6.16/1.47  
% 6.16/1.47  ------ Preprocessing Options
% 6.16/1.47  
% 6.16/1.47  --preprocessing_flag                    true
% 6.16/1.47  --time_out_prep_mult                    0.1
% 6.16/1.47  --splitting_mode                        input
% 6.16/1.47  --splitting_grd                         true
% 6.16/1.47  --splitting_cvd                         false
% 6.16/1.47  --splitting_cvd_svl                     false
% 6.16/1.47  --splitting_nvd                         32
% 6.16/1.47  --sub_typing                            true
% 6.16/1.47  --prep_gs_sim                           true
% 6.16/1.47  --prep_unflatten                        true
% 6.16/1.47  --prep_res_sim                          true
% 6.16/1.47  --prep_upred                            true
% 6.16/1.47  --prep_sem_filter                       exhaustive
% 6.16/1.47  --prep_sem_filter_out                   false
% 6.16/1.47  --pred_elim                             true
% 6.16/1.47  --res_sim_input                         true
% 6.16/1.47  --eq_ax_congr_red                       true
% 6.16/1.47  --pure_diseq_elim                       true
% 6.16/1.47  --brand_transform                       false
% 6.16/1.47  --non_eq_to_eq                          false
% 6.16/1.47  --prep_def_merge                        true
% 6.16/1.47  --prep_def_merge_prop_impl              false
% 6.16/1.47  --prep_def_merge_mbd                    true
% 6.16/1.47  --prep_def_merge_tr_red                 false
% 6.16/1.47  --prep_def_merge_tr_cl                  false
% 6.16/1.47  --smt_preprocessing                     true
% 6.16/1.47  --smt_ac_axioms                         fast
% 6.16/1.47  --preprocessed_out                      false
% 6.16/1.47  --preprocessed_stats                    false
% 6.16/1.47  
% 6.16/1.47  ------ Abstraction refinement Options
% 6.16/1.47  
% 6.16/1.47  --abstr_ref                             []
% 6.16/1.47  --abstr_ref_prep                        false
% 6.16/1.47  --abstr_ref_until_sat                   false
% 6.16/1.47  --abstr_ref_sig_restrict                funpre
% 6.16/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 6.16/1.47  --abstr_ref_under                       []
% 6.16/1.47  
% 6.16/1.47  ------ SAT Options
% 6.16/1.47  
% 6.16/1.47  --sat_mode                              false
% 6.16/1.47  --sat_fm_restart_options                ""
% 6.16/1.47  --sat_gr_def                            false
% 6.16/1.47  --sat_epr_types                         true
% 6.16/1.47  --sat_non_cyclic_types                  false
% 6.16/1.47  --sat_finite_models                     false
% 6.16/1.47  --sat_fm_lemmas                         false
% 6.16/1.47  --sat_fm_prep                           false
% 6.16/1.47  --sat_fm_uc_incr                        true
% 6.16/1.47  --sat_out_model                         small
% 6.16/1.47  --sat_out_clauses                       false
% 6.16/1.47  
% 6.16/1.47  ------ QBF Options
% 6.16/1.47  
% 6.16/1.47  --qbf_mode                              false
% 6.16/1.47  --qbf_elim_univ                         false
% 6.16/1.47  --qbf_dom_inst                          none
% 6.16/1.47  --qbf_dom_pre_inst                      false
% 6.16/1.47  --qbf_sk_in                             false
% 6.16/1.47  --qbf_pred_elim                         true
% 6.16/1.47  --qbf_split                             512
% 6.16/1.47  
% 6.16/1.47  ------ BMC1 Options
% 6.16/1.47  
% 6.16/1.47  --bmc1_incremental                      false
% 6.16/1.47  --bmc1_axioms                           reachable_all
% 6.16/1.47  --bmc1_min_bound                        0
% 6.16/1.47  --bmc1_max_bound                        -1
% 6.16/1.47  --bmc1_max_bound_default                -1
% 6.16/1.47  --bmc1_symbol_reachability              true
% 6.16/1.47  --bmc1_property_lemmas                  false
% 6.16/1.47  --bmc1_k_induction                      false
% 6.16/1.47  --bmc1_non_equiv_states                 false
% 6.16/1.47  --bmc1_deadlock                         false
% 6.16/1.47  --bmc1_ucm                              false
% 6.16/1.47  --bmc1_add_unsat_core                   none
% 6.16/1.47  --bmc1_unsat_core_children              false
% 6.16/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 6.16/1.47  --bmc1_out_stat                         full
% 6.16/1.47  --bmc1_ground_init                      false
% 6.16/1.47  --bmc1_pre_inst_next_state              false
% 6.16/1.47  --bmc1_pre_inst_state                   false
% 6.16/1.47  --bmc1_pre_inst_reach_state             false
% 6.16/1.47  --bmc1_out_unsat_core                   false
% 6.16/1.47  --bmc1_aig_witness_out                  false
% 6.16/1.47  --bmc1_verbose                          false
% 6.16/1.47  --bmc1_dump_clauses_tptp                false
% 6.16/1.47  --bmc1_dump_unsat_core_tptp             false
% 6.16/1.47  --bmc1_dump_file                        -
% 6.16/1.47  --bmc1_ucm_expand_uc_limit              128
% 6.16/1.47  --bmc1_ucm_n_expand_iterations          6
% 6.16/1.47  --bmc1_ucm_extend_mode                  1
% 6.16/1.47  --bmc1_ucm_init_mode                    2
% 6.16/1.47  --bmc1_ucm_cone_mode                    none
% 6.16/1.47  --bmc1_ucm_reduced_relation_type        0
% 6.16/1.47  --bmc1_ucm_relax_model                  4
% 6.16/1.47  --bmc1_ucm_full_tr_after_sat            true
% 6.16/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 6.16/1.47  --bmc1_ucm_layered_model                none
% 6.16/1.47  --bmc1_ucm_max_lemma_size               10
% 6.16/1.47  
% 6.16/1.47  ------ AIG Options
% 6.16/1.47  
% 6.16/1.47  --aig_mode                              false
% 6.16/1.47  
% 6.16/1.47  ------ Instantiation Options
% 6.16/1.47  
% 6.16/1.47  --instantiation_flag                    true
% 6.16/1.47  --inst_sos_flag                         false
% 6.16/1.47  --inst_sos_phase                        true
% 6.16/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.16/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.16/1.47  --inst_lit_sel_side                     num_symb
% 6.16/1.47  --inst_solver_per_active                1400
% 6.16/1.47  --inst_solver_calls_frac                1.
% 6.16/1.47  --inst_passive_queue_type               priority_queues
% 6.16/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.16/1.47  --inst_passive_queues_freq              [25;2]
% 6.16/1.47  --inst_dismatching                      true
% 6.16/1.47  --inst_eager_unprocessed_to_passive     true
% 6.16/1.47  --inst_prop_sim_given                   true
% 6.16/1.47  --inst_prop_sim_new                     false
% 6.16/1.47  --inst_subs_new                         false
% 6.16/1.47  --inst_eq_res_simp                      false
% 6.16/1.47  --inst_subs_given                       false
% 6.16/1.47  --inst_orphan_elimination               true
% 6.16/1.47  --inst_learning_loop_flag               true
% 6.16/1.47  --inst_learning_start                   3000
% 6.16/1.47  --inst_learning_factor                  2
% 6.16/1.47  --inst_start_prop_sim_after_learn       3
% 6.16/1.47  --inst_sel_renew                        solver
% 6.16/1.47  --inst_lit_activity_flag                true
% 6.16/1.47  --inst_restr_to_given                   false
% 6.16/1.47  --inst_activity_threshold               500
% 6.16/1.47  --inst_out_proof                        true
% 6.16/1.47  
% 6.16/1.47  ------ Resolution Options
% 6.16/1.47  
% 6.16/1.47  --resolution_flag                       true
% 6.16/1.47  --res_lit_sel                           adaptive
% 6.16/1.47  --res_lit_sel_side                      none
% 6.16/1.47  --res_ordering                          kbo
% 6.16/1.47  --res_to_prop_solver                    active
% 6.16/1.47  --res_prop_simpl_new                    false
% 6.16/1.47  --res_prop_simpl_given                  true
% 6.16/1.47  --res_passive_queue_type                priority_queues
% 6.16/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.16/1.47  --res_passive_queues_freq               [15;5]
% 6.16/1.47  --res_forward_subs                      full
% 6.16/1.47  --res_backward_subs                     full
% 6.16/1.47  --res_forward_subs_resolution           true
% 6.16/1.47  --res_backward_subs_resolution          true
% 6.16/1.47  --res_orphan_elimination                true
% 6.16/1.47  --res_time_limit                        2.
% 6.16/1.47  --res_out_proof                         true
% 6.16/1.47  
% 6.16/1.47  ------ Superposition Options
% 6.16/1.47  
% 6.16/1.47  --superposition_flag                    true
% 6.16/1.47  --sup_passive_queue_type                priority_queues
% 6.16/1.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.16/1.47  --sup_passive_queues_freq               [8;1;4]
% 6.16/1.47  --demod_completeness_check              fast
% 6.16/1.47  --demod_use_ground                      true
% 6.16/1.47  --sup_to_prop_solver                    passive
% 6.16/1.47  --sup_prop_simpl_new                    true
% 6.16/1.47  --sup_prop_simpl_given                  true
% 6.16/1.47  --sup_fun_splitting                     false
% 6.16/1.47  --sup_smt_interval                      50000
% 6.16/1.47  
% 6.16/1.47  ------ Superposition Simplification Setup
% 6.16/1.47  
% 6.16/1.47  --sup_indices_passive                   []
% 6.16/1.47  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.16/1.47  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.16/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.16/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 6.16/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.16/1.47  --sup_full_bw                           [BwDemod]
% 6.16/1.47  --sup_immed_triv                        [TrivRules]
% 6.16/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.16/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.16/1.47  --sup_immed_bw_main                     []
% 6.16/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.16/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 6.16/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.16/1.47  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.16/1.47  
% 6.16/1.47  ------ Combination Options
% 6.16/1.47  
% 6.16/1.47  --comb_res_mult                         3
% 6.16/1.47  --comb_sup_mult                         2
% 6.16/1.47  --comb_inst_mult                        10
% 6.16/1.47  
% 6.16/1.47  ------ Debug Options
% 6.16/1.47  
% 6.16/1.47  --dbg_backtrace                         false
% 6.16/1.47  --dbg_dump_prop_clauses                 false
% 6.16/1.47  --dbg_dump_prop_clauses_file            -
% 6.16/1.47  --dbg_out_stat                          false
% 6.16/1.47  ------ Parsing...
% 6.16/1.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.16/1.47  
% 6.16/1.47  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 6.16/1.47  
% 6.16/1.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.16/1.47  
% 6.16/1.47  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 6.16/1.47  ------ Proving...
% 6.16/1.47  ------ Problem Properties 
% 6.16/1.47  
% 6.16/1.47  
% 6.16/1.47  clauses                                 9
% 6.16/1.47  conjectures                             1
% 6.16/1.47  EPR                                     0
% 6.16/1.47  Horn                                    9
% 6.16/1.47  unary                                   9
% 6.16/1.47  binary                                  0
% 6.16/1.47  lits                                    9
% 6.16/1.47  lits eq                                 9
% 6.16/1.47  fd_pure                                 0
% 6.16/1.47  fd_pseudo                               0
% 6.16/1.47  fd_cond                                 0
% 6.16/1.47  fd_pseudo_cond                          0
% 6.16/1.47  AC symbols                              0
% 6.16/1.47  
% 6.16/1.47  ------ Schedule UEQ
% 6.16/1.47  
% 6.16/1.47  ------ pure equality problem: resolution off 
% 6.16/1.47  
% 6.16/1.47  ------ Option_UEQ Time Limit: Unbounded
% 6.16/1.47  
% 6.16/1.47  
% 6.16/1.47  ------ 
% 6.16/1.47  Current options:
% 6.16/1.47  ------ 
% 6.16/1.47  
% 6.16/1.47  ------ Input Options
% 6.16/1.47  
% 6.16/1.47  --out_options                           all
% 6.16/1.47  --tptp_safe_out                         true
% 6.16/1.47  --problem_path                          ""
% 6.16/1.47  --include_path                          ""
% 6.16/1.47  --clausifier                            res/vclausify_rel
% 6.16/1.47  --clausifier_options                    --mode clausify
% 6.16/1.47  --stdin                                 false
% 6.16/1.47  --stats_out                             all
% 6.16/1.47  
% 6.16/1.47  ------ General Options
% 6.16/1.47  
% 6.16/1.47  --fof                                   false
% 6.16/1.47  --time_out_real                         305.
% 6.16/1.47  --time_out_virtual                      -1.
% 6.16/1.47  --symbol_type_check                     false
% 6.16/1.47  --clausify_out                          false
% 6.16/1.47  --sig_cnt_out                           false
% 6.16/1.47  --trig_cnt_out                          false
% 6.16/1.47  --trig_cnt_out_tolerance                1.
% 6.16/1.47  --trig_cnt_out_sk_spl                   false
% 6.16/1.47  --abstr_cl_out                          false
% 6.16/1.47  
% 6.16/1.47  ------ Global Options
% 6.16/1.47  
% 6.16/1.47  --schedule                              default
% 6.16/1.47  --add_important_lit                     false
% 6.16/1.47  --prop_solver_per_cl                    1000
% 6.16/1.47  --min_unsat_core                        false
% 6.16/1.47  --soft_assumptions                      false
% 6.16/1.47  --soft_lemma_size                       3
% 6.16/1.47  --prop_impl_unit_size                   0
% 6.16/1.47  --prop_impl_unit                        []
% 6.16/1.47  --share_sel_clauses                     true
% 6.16/1.47  --reset_solvers                         false
% 6.16/1.47  --bc_imp_inh                            [conj_cone]
% 6.16/1.47  --conj_cone_tolerance                   3.
% 6.16/1.47  --extra_neg_conj                        none
% 6.16/1.47  --large_theory_mode                     true
% 6.16/1.47  --prolific_symb_bound                   200
% 6.16/1.47  --lt_threshold                          2000
% 6.16/1.47  --clause_weak_htbl                      true
% 6.16/1.47  --gc_record_bc_elim                     false
% 6.16/1.47  
% 6.16/1.47  ------ Preprocessing Options
% 6.16/1.47  
% 6.16/1.47  --preprocessing_flag                    true
% 6.16/1.47  --time_out_prep_mult                    0.1
% 6.16/1.47  --splitting_mode                        input
% 6.16/1.47  --splitting_grd                         true
% 6.16/1.47  --splitting_cvd                         false
% 6.16/1.47  --splitting_cvd_svl                     false
% 6.16/1.47  --splitting_nvd                         32
% 6.16/1.47  --sub_typing                            true
% 6.16/1.47  --prep_gs_sim                           true
% 6.16/1.47  --prep_unflatten                        true
% 6.16/1.47  --prep_res_sim                          true
% 6.16/1.47  --prep_upred                            true
% 6.16/1.47  --prep_sem_filter                       exhaustive
% 6.16/1.47  --prep_sem_filter_out                   false
% 6.16/1.47  --pred_elim                             true
% 6.16/1.47  --res_sim_input                         true
% 6.16/1.47  --eq_ax_congr_red                       true
% 6.16/1.47  --pure_diseq_elim                       true
% 6.16/1.47  --brand_transform                       false
% 6.16/1.47  --non_eq_to_eq                          false
% 6.16/1.47  --prep_def_merge                        true
% 6.16/1.47  --prep_def_merge_prop_impl              false
% 6.16/1.47  --prep_def_merge_mbd                    true
% 6.16/1.47  --prep_def_merge_tr_red                 false
% 6.16/1.47  --prep_def_merge_tr_cl                  false
% 6.16/1.47  --smt_preprocessing                     true
% 6.16/1.47  --smt_ac_axioms                         fast
% 6.16/1.47  --preprocessed_out                      false
% 6.16/1.47  --preprocessed_stats                    false
% 6.16/1.47  
% 6.16/1.47  ------ Abstraction refinement Options
% 6.16/1.47  
% 6.16/1.47  --abstr_ref                             []
% 6.16/1.47  --abstr_ref_prep                        false
% 6.16/1.47  --abstr_ref_until_sat                   false
% 6.16/1.47  --abstr_ref_sig_restrict                funpre
% 6.16/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 6.16/1.47  --abstr_ref_under                       []
% 6.16/1.47  
% 6.16/1.47  ------ SAT Options
% 6.16/1.47  
% 6.16/1.47  --sat_mode                              false
% 6.16/1.47  --sat_fm_restart_options                ""
% 6.16/1.47  --sat_gr_def                            false
% 6.16/1.47  --sat_epr_types                         true
% 6.16/1.47  --sat_non_cyclic_types                  false
% 6.16/1.47  --sat_finite_models                     false
% 6.16/1.47  --sat_fm_lemmas                         false
% 6.16/1.47  --sat_fm_prep                           false
% 6.16/1.47  --sat_fm_uc_incr                        true
% 6.16/1.47  --sat_out_model                         small
% 6.16/1.47  --sat_out_clauses                       false
% 6.16/1.47  
% 6.16/1.47  ------ QBF Options
% 6.16/1.47  
% 6.16/1.47  --qbf_mode                              false
% 6.16/1.47  --qbf_elim_univ                         false
% 6.16/1.47  --qbf_dom_inst                          none
% 6.16/1.47  --qbf_dom_pre_inst                      false
% 6.16/1.47  --qbf_sk_in                             false
% 6.16/1.47  --qbf_pred_elim                         true
% 6.16/1.47  --qbf_split                             512
% 6.16/1.47  
% 6.16/1.47  ------ BMC1 Options
% 6.16/1.47  
% 6.16/1.47  --bmc1_incremental                      false
% 6.16/1.47  --bmc1_axioms                           reachable_all
% 6.16/1.47  --bmc1_min_bound                        0
% 6.16/1.47  --bmc1_max_bound                        -1
% 6.16/1.47  --bmc1_max_bound_default                -1
% 6.16/1.47  --bmc1_symbol_reachability              true
% 6.16/1.47  --bmc1_property_lemmas                  false
% 6.16/1.47  --bmc1_k_induction                      false
% 6.16/1.47  --bmc1_non_equiv_states                 false
% 6.16/1.47  --bmc1_deadlock                         false
% 6.16/1.47  --bmc1_ucm                              false
% 6.16/1.47  --bmc1_add_unsat_core                   none
% 6.16/1.47  --bmc1_unsat_core_children              false
% 6.16/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 6.16/1.47  --bmc1_out_stat                         full
% 6.16/1.47  --bmc1_ground_init                      false
% 6.16/1.47  --bmc1_pre_inst_next_state              false
% 6.16/1.47  --bmc1_pre_inst_state                   false
% 6.16/1.47  --bmc1_pre_inst_reach_state             false
% 6.16/1.47  --bmc1_out_unsat_core                   false
% 6.16/1.47  --bmc1_aig_witness_out                  false
% 6.16/1.47  --bmc1_verbose                          false
% 6.16/1.47  --bmc1_dump_clauses_tptp                false
% 6.16/1.47  --bmc1_dump_unsat_core_tptp             false
% 6.16/1.47  --bmc1_dump_file                        -
% 6.16/1.47  --bmc1_ucm_expand_uc_limit              128
% 6.16/1.47  --bmc1_ucm_n_expand_iterations          6
% 6.16/1.47  --bmc1_ucm_extend_mode                  1
% 6.16/1.47  --bmc1_ucm_init_mode                    2
% 6.16/1.47  --bmc1_ucm_cone_mode                    none
% 6.16/1.47  --bmc1_ucm_reduced_relation_type        0
% 6.16/1.47  --bmc1_ucm_relax_model                  4
% 6.16/1.47  --bmc1_ucm_full_tr_after_sat            true
% 6.16/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 6.16/1.47  --bmc1_ucm_layered_model                none
% 6.16/1.47  --bmc1_ucm_max_lemma_size               10
% 6.16/1.47  
% 6.16/1.47  ------ AIG Options
% 6.16/1.47  
% 6.16/1.47  --aig_mode                              false
% 6.16/1.47  
% 6.16/1.47  ------ Instantiation Options
% 6.16/1.47  
% 6.16/1.47  --instantiation_flag                    false
% 6.16/1.47  --inst_sos_flag                         false
% 6.16/1.47  --inst_sos_phase                        true
% 6.16/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.16/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.16/1.47  --inst_lit_sel_side                     num_symb
% 6.16/1.47  --inst_solver_per_active                1400
% 6.16/1.47  --inst_solver_calls_frac                1.
% 6.16/1.47  --inst_passive_queue_type               priority_queues
% 6.16/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.16/1.47  --inst_passive_queues_freq              [25;2]
% 6.16/1.47  --inst_dismatching                      true
% 6.16/1.47  --inst_eager_unprocessed_to_passive     true
% 6.16/1.47  --inst_prop_sim_given                   true
% 6.16/1.47  --inst_prop_sim_new                     false
% 6.16/1.47  --inst_subs_new                         false
% 6.16/1.47  --inst_eq_res_simp                      false
% 6.16/1.47  --inst_subs_given                       false
% 6.16/1.47  --inst_orphan_elimination               true
% 6.16/1.47  --inst_learning_loop_flag               true
% 6.16/1.47  --inst_learning_start                   3000
% 6.16/1.47  --inst_learning_factor                  2
% 6.16/1.47  --inst_start_prop_sim_after_learn       3
% 6.16/1.47  --inst_sel_renew                        solver
% 6.16/1.47  --inst_lit_activity_flag                true
% 6.16/1.47  --inst_restr_to_given                   false
% 6.16/1.47  --inst_activity_threshold               500
% 6.16/1.47  --inst_out_proof                        true
% 6.16/1.47  
% 6.16/1.47  ------ Resolution Options
% 6.16/1.47  
% 6.16/1.47  --resolution_flag                       false
% 6.16/1.47  --res_lit_sel                           adaptive
% 6.16/1.47  --res_lit_sel_side                      none
% 6.16/1.47  --res_ordering                          kbo
% 6.16/1.47  --res_to_prop_solver                    active
% 6.16/1.47  --res_prop_simpl_new                    false
% 6.16/1.47  --res_prop_simpl_given                  true
% 6.16/1.47  --res_passive_queue_type                priority_queues
% 6.16/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.16/1.47  --res_passive_queues_freq               [15;5]
% 6.16/1.47  --res_forward_subs                      full
% 6.16/1.47  --res_backward_subs                     full
% 6.16/1.47  --res_forward_subs_resolution           true
% 6.16/1.47  --res_backward_subs_resolution          true
% 6.16/1.47  --res_orphan_elimination                true
% 6.16/1.47  --res_time_limit                        2.
% 6.16/1.47  --res_out_proof                         true
% 6.16/1.47  
% 6.16/1.47  ------ Superposition Options
% 6.16/1.47  
% 6.16/1.47  --superposition_flag                    true
% 6.16/1.47  --sup_passive_queue_type                priority_queues
% 6.16/1.47  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.16/1.47  --sup_passive_queues_freq               [8;1;4]
% 6.16/1.47  --demod_completeness_check              fast
% 6.16/1.47  --demod_use_ground                      true
% 6.16/1.47  --sup_to_prop_solver                    active
% 6.16/1.47  --sup_prop_simpl_new                    false
% 6.16/1.47  --sup_prop_simpl_given                  false
% 6.16/1.47  --sup_fun_splitting                     true
% 6.16/1.47  --sup_smt_interval                      10000
% 6.16/1.47  
% 6.16/1.47  ------ Superposition Simplification Setup
% 6.16/1.47  
% 6.16/1.47  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 6.16/1.47  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 6.16/1.47  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 6.16/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.16/1.47  --sup_full_triv                         [TrivRules]
% 6.16/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 6.16/1.47  --sup_full_bw                           [BwDemod;BwSubsumption]
% 6.16/1.47  --sup_immed_triv                        [TrivRules]
% 6.16/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.16/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 6.16/1.47  --sup_immed_bw_main                     []
% 6.16/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 6.16/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 6.16/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 6.16/1.47  --sup_input_bw                          [BwDemod;BwSubsumption]
% 6.16/1.47  
% 6.16/1.47  ------ Combination Options
% 6.16/1.47  
% 6.16/1.47  --comb_res_mult                         1
% 6.16/1.47  --comb_sup_mult                         1
% 6.16/1.47  --comb_inst_mult                        1000000
% 6.16/1.47  
% 6.16/1.47  ------ Debug Options
% 6.16/1.47  
% 6.16/1.47  --dbg_backtrace                         false
% 6.16/1.47  --dbg_dump_prop_clauses                 false
% 6.16/1.47  --dbg_dump_prop_clauses_file            -
% 6.16/1.47  --dbg_out_stat                          false
% 6.16/1.47  
% 6.16/1.47  
% 6.16/1.47  
% 6.16/1.47  
% 6.16/1.47  ------ Proving...
% 6.16/1.47  
% 6.16/1.47  
% 6.16/1.47  % SZS status Theorem for theBenchmark.p
% 6.16/1.47  
% 6.16/1.47   Resolution empty clause
% 6.16/1.47  
% 6.16/1.47  % SZS output start CNFRefutation for theBenchmark.p
% 6.16/1.47  
% 6.16/1.47  fof(f4,axiom,(
% 6.16/1.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 6.16/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.16/1.47  
% 6.16/1.47  fof(f19,plain,(
% 6.16/1.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 6.16/1.47    inference(cnf_transformation,[],[f4])).
% 6.16/1.47  
% 6.16/1.47  fof(f7,axiom,(
% 6.16/1.47    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 6.16/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.16/1.47  
% 6.16/1.47  fof(f22,plain,(
% 6.16/1.47    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 6.16/1.47    inference(cnf_transformation,[],[f7])).
% 6.16/1.47  
% 6.16/1.47  fof(f3,axiom,(
% 6.16/1.47    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 6.16/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.16/1.47  
% 6.16/1.47  fof(f18,plain,(
% 6.16/1.47    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 6.16/1.47    inference(cnf_transformation,[],[f3])).
% 6.16/1.47  
% 6.16/1.47  fof(f8,axiom,(
% 6.16/1.47    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 6.16/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.16/1.47  
% 6.16/1.47  fof(f23,plain,(
% 6.16/1.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 6.16/1.47    inference(cnf_transformation,[],[f8])).
% 6.16/1.47  
% 6.16/1.47  fof(f27,plain,(
% 6.16/1.47    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 6.16/1.47    inference(definition_unfolding,[],[f18,f23])).
% 6.16/1.47  
% 6.16/1.47  fof(f5,axiom,(
% 6.16/1.47    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 6.16/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.16/1.47  
% 6.16/1.47  fof(f20,plain,(
% 6.16/1.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.16/1.47    inference(cnf_transformation,[],[f5])).
% 6.16/1.47  
% 6.16/1.47  fof(f10,axiom,(
% 6.16/1.47    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 6.16/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.16/1.47  
% 6.16/1.47  fof(f25,plain,(
% 6.16/1.47    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 6.16/1.47    inference(cnf_transformation,[],[f10])).
% 6.16/1.47  
% 6.16/1.47  fof(f29,plain,(
% 6.16/1.47    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 6.16/1.47    inference(definition_unfolding,[],[f25,f23])).
% 6.16/1.47  
% 6.16/1.47  fof(f1,axiom,(
% 6.16/1.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 6.16/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.16/1.47  
% 6.16/1.47  fof(f16,plain,(
% 6.16/1.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 6.16/1.47    inference(cnf_transformation,[],[f1])).
% 6.16/1.47  
% 6.16/1.47  fof(f6,axiom,(
% 6.16/1.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 6.16/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.16/1.47  
% 6.16/1.47  fof(f21,plain,(
% 6.16/1.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 6.16/1.47    inference(cnf_transformation,[],[f6])).
% 6.16/1.47  
% 6.16/1.47  fof(f9,axiom,(
% 6.16/1.47    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 6.16/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.16/1.47  
% 6.16/1.47  fof(f24,plain,(
% 6.16/1.47    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 6.16/1.47    inference(cnf_transformation,[],[f9])).
% 6.16/1.47  
% 6.16/1.47  fof(f28,plain,(
% 6.16/1.47    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 6.16/1.47    inference(definition_unfolding,[],[f24,f23])).
% 6.16/1.47  
% 6.16/1.47  fof(f11,conjecture,(
% 6.16/1.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 6.16/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.16/1.47  
% 6.16/1.47  fof(f12,negated_conjecture,(
% 6.16/1.47    ~! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 6.16/1.47    inference(negated_conjecture,[],[f11])).
% 6.16/1.47  
% 6.16/1.47  fof(f13,plain,(
% 6.16/1.47    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 6.16/1.47    inference(ennf_transformation,[],[f12])).
% 6.16/1.47  
% 6.16/1.47  fof(f14,plain,(
% 6.16/1.47    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 6.16/1.47    introduced(choice_axiom,[])).
% 6.16/1.47  
% 6.16/1.47  fof(f15,plain,(
% 6.16/1.47    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 6.16/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 6.16/1.47  
% 6.16/1.47  fof(f26,plain,(
% 6.16/1.47    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 6.16/1.47    inference(cnf_transformation,[],[f15])).
% 6.16/1.47  
% 6.16/1.47  fof(f2,axiom,(
% 6.16/1.47    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 6.16/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.16/1.47  
% 6.16/1.47  fof(f17,plain,(
% 6.16/1.47    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 6.16/1.47    inference(cnf_transformation,[],[f2])).
% 6.16/1.47  
% 6.16/1.47  fof(f30,plain,(
% 6.16/1.47    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 6.16/1.47    inference(definition_unfolding,[],[f26,f17,f23])).
% 6.16/1.47  
% 6.16/1.47  cnf(c_2,plain,
% 6.16/1.47      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 6.16/1.47      inference(cnf_transformation,[],[f19]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_5,plain,
% 6.16/1.47      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 6.16/1.47      inference(cnf_transformation,[],[f22]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_1,plain,
% 6.16/1.47      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 6.16/1.47      inference(cnf_transformation,[],[f27]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_3,plain,
% 6.16/1.47      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 6.16/1.47      inference(cnf_transformation,[],[f20]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_27,plain,
% 6.16/1.47      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 6.16/1.47      inference(light_normalisation,[status(thm)],[c_1,c_3]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_67,plain,
% 6.16/1.47      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_5,c_27]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_68,plain,
% 6.16/1.47      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_67,c_2]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_174,plain,
% 6.16/1.47      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_2,c_68]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_358,plain,
% 6.16/1.47      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_174,c_5]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_7,plain,
% 6.16/1.47      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
% 6.16/1.47      inference(cnf_transformation,[],[f29]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_103,plain,
% 6.16/1.47      ( k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(X0,k1_xboole_0)) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_27,c_7]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_0,plain,
% 6.16/1.47      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 6.16/1.47      inference(cnf_transformation,[],[f16]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_30,plain,
% 6.16/1.47      ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_27,c_2]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_32,plain,
% 6.16/1.47      ( k2_xboole_0(X0,X0) = k2_xboole_0(k1_xboole_0,X0) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_0,c_30]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_4,plain,
% 6.16/1.47      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 6.16/1.47      inference(cnf_transformation,[],[f21]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_47,plain,
% 6.16/1.47      ( k4_xboole_0(k2_xboole_0(X0,X0),X0) = k4_xboole_0(k1_xboole_0,X0) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_32,c_4]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_111,plain,
% 6.16/1.47      ( k4_xboole_0(k1_xboole_0,X0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 6.16/1.47      inference(light_normalisation,[status(thm)],[c_103,c_3,c_27,c_47]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_6,plain,
% 6.16/1.47      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 6.16/1.47      inference(cnf_transformation,[],[f28]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_79,plain,
% 6.16/1.47      ( k2_xboole_0(k4_xboole_0(X0,X0),X0) = X0 ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_3,c_6]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_88,plain,
% 6.16/1.47      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 6.16/1.47      inference(light_normalisation,[status(thm)],[c_79,c_27]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_112,plain,
% 6.16/1.47      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_111,c_88]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_361,plain,
% 6.16/1.47      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k1_xboole_0 ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_358,c_5,c_112]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_66,plain,
% 6.16/1.47      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_5,c_5]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_69,plain,
% 6.16/1.47      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_66,c_5]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_2731,plain,
% 6.16/1.47      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,k2_xboole_0(X0,X2))) = k1_xboole_0 ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_361,c_69]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_179,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_68,c_2]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_51,plain,
% 6.16/1.47      ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_4,c_3]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_54,plain,
% 6.16/1.47      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 6.16/1.47      inference(light_normalisation,[status(thm)],[c_51,c_3]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_189,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_179,c_54]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_420,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_0,c_189]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_668,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_2,c_420]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_708,plain,
% 6.16/1.47      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_668,c_420]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_10238,plain,
% 6.16/1.47      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X1,k2_xboole_0(X0,X2))) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_2731,c_708]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_172,plain,
% 6.16/1.47      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_0,c_68]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_202,plain,
% 6.16/1.47      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_172,c_5]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_204,plain,
% 6.16/1.47      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k1_xboole_0 ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_202,c_69,c_112]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_445,plain,
% 6.16/1.47      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X0,X2))) = k1_xboole_0 ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_0,c_204]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_44,plain,
% 6.16/1.47      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_0,c_4]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_216,plain,
% 6.16/1.47      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_44,c_2]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_226,plain,
% 6.16/1.47      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 6.16/1.47      inference(light_normalisation,[status(thm)],[c_216,c_2]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_550,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X1) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_189,c_226]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_52,plain,
% 6.16/1.47      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_4,c_2]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_53,plain,
% 6.16/1.47      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 6.16/1.47      inference(light_normalisation,[status(thm)],[c_52,c_2]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_560,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_226,c_53]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_564,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 6.16/1.47      inference(light_normalisation,[status(thm)],[c_560,c_420]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_570,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_550,c_564]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_979,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_2,c_570]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_175,plain,
% 6.16/1.47      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_6,c_68]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_242,plain,
% 6.16/1.47      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_175,c_2]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_254,plain,
% 6.16/1.47      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 6.16/1.47      inference(light_normalisation,[status(thm)],[c_242,c_54]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_286,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_44,c_254]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_1031,plain,
% 6.16/1.47      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 6.16/1.47      inference(light_normalisation,[status(thm)],[c_979,c_286]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_1819,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k2_xboole_0(X1,X2))) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_445,c_1031]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_953,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_445,c_2]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_269,plain,
% 6.16/1.47      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_53,c_68]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_835,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_269,c_2]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_425,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k2_xboole_0(X1,X0)) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_53,c_189]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_434,plain,
% 6.16/1.47      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_189,c_0]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_441,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_425,c_434]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_853,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 6.16/1.47      inference(light_normalisation,[status(thm)],[c_835,c_441]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_970,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k2_xboole_0(k2_xboole_0(X1,X2),X0) ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_953,c_853]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_1878,plain,
% 6.16/1.47      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(k2_xboole_0(X1,X2),X0) ),
% 6.16/1.47      inference(light_normalisation,[status(thm)],[c_1819,c_970]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_220,plain,
% 6.16/1.47      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k4_xboole_0(X1,X0),X2) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_44,c_5]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_221,plain,
% 6.16/1.47      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_220,c_5]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_2922,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_0,c_286]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_9112,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X0,X1)) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_221,c_2922]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_247,plain,
% 6.16/1.47      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_175,c_5]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_249,plain,
% 6.16/1.47      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_247,c_5,c_112]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_602,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_249,c_2]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_617,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k2_xboole_0(X0,X1) ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_602,c_54]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_9140,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(X1,k2_xboole_0(X0,X3))) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_221,c_617]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_9118,plain,
% 6.16/1.47      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X1,X2)) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_221,c_708]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_9172,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(k2_xboole_0(X0,X2),X1) ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_9118,c_1031]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_9177,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X2),X1) ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_9112,c_9140,c_9172]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_46,plain,
% 6.16/1.47      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_2,c_4]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_1639,plain,
% 6.16/1.47      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_46,c_708]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_1672,plain,
% 6.16/1.47      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_708,c_0]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_1715,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_1639,c_708,c_1672]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_9178,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_9177,c_1715]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_589,plain,
% 6.16/1.47      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_0,c_249]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_2421,plain,
% 6.16/1.47      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X3,X0))) = k1_xboole_0 ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_69,c_589]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_10014,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X2,X3)),k1_xboole_0) = k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X2,X3)) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_2421,c_286]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_10029,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X2,X3)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k2_xboole_0(X1,X2))) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_2421,c_1031]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_183,plain,
% 6.16/1.47      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_68,c_5]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_185,plain,
% 6.16/1.47      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k1_xboole_0 ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_183,c_69,c_112]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_385,plain,
% 6.16/1.47      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k1_xboole_0 ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_0,c_185]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_2420,plain,
% 6.16/1.47      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X0)))) = k1_xboole_0 ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_69,c_385]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_65,plain,
% 6.16/1.47      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_5,c_2]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_9858,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X2,X3)) = k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_2420,c_65]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_9867,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X2,X3)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_9858,c_853,c_9178]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_10073,plain,
% 6.16/1.47      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 6.16/1.47      inference(light_normalisation,[status(thm)],[c_10029,c_1878,c_9867]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_10086,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(k2_xboole_0(X3,X1),k1_xboole_0)) = k2_xboole_0(X1,k2_xboole_0(X3,k2_xboole_0(X0,k4_xboole_0(X1,X2)))) ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_10014,c_10073]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_10025,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X3,X0))),k1_xboole_0) = k2_xboole_0(k2_xboole_0(X2,k2_xboole_0(X3,X0)),k4_xboole_0(X0,X1)) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_2421,c_2922]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_10030,plain,
% 6.16/1.47      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X3,X0))) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X2,k2_xboole_0(X3,X0))) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_2421,c_708]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_10072,plain,
% 6.16/1.47      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X3,X0))) = k2_xboole_0(X0,k2_xboole_0(X3,X2)) ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_10030,c_1878,c_9178]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_10075,plain,
% 6.16/1.47      ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X0,X3)))) = k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X0,k1_xboole_0)) ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_10025,c_10072,c_10073]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_10076,plain,
% 6.16/1.47      ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X0,X3)))) = k2_xboole_0(X2,k2_xboole_0(X1,k2_xboole_0(X0,k1_xboole_0))) ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_10075,c_10073]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_10077,plain,
% 6.16/1.47      ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X0,X3)))) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 6.16/1.47      inference(light_normalisation,[status(thm)],[c_10076,c_54]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_10087,plain,
% 6.16/1.47      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X0,k2_xboole_0(X3,k1_xboole_0)))) = k2_xboole_0(X2,k2_xboole_0(X3,X0)) ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_10086,c_10073,c_10077]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_10088,plain,
% 6.16/1.47      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X0,X3))) = k2_xboole_0(X2,k2_xboole_0(X3,X0)) ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_10087,c_54]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_10281,plain,
% 6.16/1.47      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_10238,c_1878,c_9178,c_10088]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_8,negated_conjecture,
% 6.16/1.47      ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
% 6.16/1.47      inference(cnf_transformation,[],[f30]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_29,plain,
% 6.16/1.47      ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) != k2_xboole_0(sK0,sK1) ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_0,c_8]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_19650,plain,
% 6.16/1.47      ( k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_10281,c_29]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_1652,plain,
% 6.16/1.47      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X2,X0)) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_589,c_708]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_1702,plain,
% 6.16/1.47      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_1652,c_88]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_7891,plain,
% 6.16/1.47      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X2,X0) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_0,c_1702]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_203,plain,
% 6.16/1.47      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k1_xboole_0 ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_172,c_5]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_488,plain,
% 6.16/1.47      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X0),X0)) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_4,c_46]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_537,plain,
% 6.16/1.47      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(X0,X1),X1)) ),
% 6.16/1.47      inference(light_normalisation,[status(thm)],[c_488,c_434]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_538,plain,
% 6.16/1.47      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_537,c_4]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_15049,plain,
% 6.16/1.47      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)),k4_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)))) = k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2))),k1_xboole_0) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_203,c_538]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_261,plain,
% 6.16/1.47      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_6,c_53]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_84,plain,
% 6.16/1.47      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_276,plain,
% 6.16/1.47      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 6.16/1.47      inference(light_normalisation,[status(thm)],[c_261,c_84]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_61,plain,
% 6.16/1.47      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_4,c_5]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_71,plain,
% 6.16/1.47      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_61,c_5]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_4065,plain,
% 6.16/1.47      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),X1)) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_276,c_71]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_4172,plain,
% 6.16/1.47      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,X1) ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_4065,c_276]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_10900,plain,
% 6.16/1.47      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X3)) = k2_xboole_0(X3,k2_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_4172,c_7891]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_611,plain,
% 6.16/1.47      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X2),X3)) = k4_xboole_0(k1_xboole_0,X3) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_249,c_5]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_613,plain,
% 6.16/1.47      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X2),X3)) = k1_xboole_0 ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_611,c_5,c_112]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_2877,plain,
% 6.16/1.47      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X2),X3)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(X0,X2),X3)) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_613,c_708]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_1640,plain,
% 6.16/1.47      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_172,c_708]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_689,plain,
% 6.16/1.47      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_420,c_0]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_1714,plain,
% 6.16/1.47      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 6.16/1.47      inference(light_normalisation,[status(thm)],[c_1640,c_689]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_2907,plain,
% 6.16/1.47      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X2),X3)) = k2_xboole_0(X3,k2_xboole_0(X0,X2)) ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_2877,c_1714]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_10233,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,k2_xboole_0(X0,X2))),k1_xboole_0) = k2_xboole_0(k2_xboole_0(X1,k2_xboole_0(X0,X2)),k4_xboole_0(X0,X1)) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_2731,c_2922]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_10237,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,X0)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k2_xboole_0(X1,X2))) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_2731,c_1031]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_10282,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X1,X2),X0) ),
% 6.16/1.47      inference(light_normalisation,[status(thm)],[c_10237,c_1878]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_2414,plain,
% 6.16/1.47      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X0,X3)))) = k1_xboole_0 ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_69,c_445]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_8595,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,X3)) = k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_2414,c_65]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_8601,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,X3)) = k2_xboole_0(k2_xboole_0(X1,X2),X0) ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_8595,c_853]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_10283,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,X0)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_10282,c_8601,c_9178]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_10285,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,k2_xboole_0(X0,X2))),k1_xboole_0) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_10233,c_10283]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_9821,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))),X3) = k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))),k1_xboole_0) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_2420,c_2]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_9833,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))),X3) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3)))) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_2420,c_1031]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_9881,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))),X3) = k2_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X1,X0)) ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_9833,c_1878,c_9178]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_9882,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))),X3) = k2_xboole_0(X3,k2_xboole_0(X2,k2_xboole_0(X1,X0))) ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_9881,c_9178]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_9888,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))),k1_xboole_0) = k2_xboole_0(X3,k2_xboole_0(X2,k2_xboole_0(X1,X0))) ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_9821,c_9882]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_10286,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_10285,c_853,c_9888,c_10088]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_10974,plain,
% 6.16/1.47      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X3) = k2_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X0,X1))) ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_10900,c_2907,c_7891,c_10286]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_2837,plain,
% 6.16/1.47      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X0,X3))) = k1_xboole_0 ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_689,c_613]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_80,plain,
% 6.16/1.47      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_4,c_6]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_6107,plain,
% 6.16/1.47      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 6.16/1.47      inference(light_normalisation,[status(thm)],[c_80,c_80,c_538]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_10532,plain,
% 6.16/1.47      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X0,X3))) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X2,k2_xboole_0(X0,X3)),k1_xboole_0),k1_xboole_0) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_2837,c_6107]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_10604,plain,
% 6.16/1.47      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0),k1_xboole_0) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 6.16/1.47      inference(light_normalisation,[status(thm)],[c_10532,c_10088]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_10605,plain,
% 6.16/1.47      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_10604,c_3,c_853,c_1031]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_4043,plain,
% 6.16/1.47      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k1_xboole_0,X2)) = k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(k1_xboole_0,X2)) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_853,c_71]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_60,plain,
% 6.16/1.47      ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,X1) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_3,c_5]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_4199,plain,
% 6.16/1.47      ( k4_xboole_0(k2_xboole_0(X0,X1),X2) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_4043,c_60]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_13062,plain,
% 6.16/1.47      ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_4199,c_3]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_13217,plain,
% 6.16/1.47      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 6.16/1.47      inference(superposition,[status(thm)],[c_10605,c_13062]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_15232,plain,
% 6.16/1.47      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 6.16/1.47      inference(demodulation,
% 6.16/1.47                [status(thm)],
% 6.16/1.47                [c_15049,c_203,c_10077,c_10974,c_13217]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_19651,plain,
% 6.16/1.47      ( k2_xboole_0(sK1,sK0) != k2_xboole_0(sK0,sK1) ),
% 6.16/1.47      inference(demodulation,[status(thm)],[c_19650,c_1031,c_7891,c_15232]) ).
% 6.16/1.47  
% 6.16/1.47  cnf(c_20205,plain,
% 6.16/1.47      ( $false ),
% 6.16/1.47      inference(theory_normalisation,[status(thm)],[c_19651]) ).
% 6.16/1.47  
% 6.16/1.47  
% 6.16/1.47  % SZS output end CNFRefutation for theBenchmark.p
% 6.16/1.47  
% 6.16/1.47  ------                               Statistics
% 6.16/1.47  
% 6.16/1.47  ------ General
% 6.16/1.47  
% 6.16/1.47  abstr_ref_over_cycles:                  0
% 6.16/1.47  abstr_ref_under_cycles:                 0
% 6.16/1.47  gc_basic_clause_elim:                   0
% 6.16/1.47  forced_gc_time:                         0
% 6.16/1.47  parsing_time:                           0.008
% 6.16/1.47  unif_index_cands_time:                  0.
% 6.16/1.47  unif_index_add_time:                    0.
% 6.16/1.47  orderings_time:                         0.
% 6.16/1.47  out_proof_time:                         0.009
% 6.16/1.47  total_time:                             0.52
% 6.16/1.47  num_of_symbols:                         36
% 6.16/1.47  num_of_terms:                           28162
% 6.16/1.47  
% 6.16/1.47  ------ Preprocessing
% 6.16/1.47  
% 6.16/1.47  num_of_splits:                          0
% 6.16/1.47  num_of_split_atoms:                     0
% 6.16/1.47  num_of_reused_defs:                     0
% 6.16/1.47  num_eq_ax_congr_red:                    0
% 6.16/1.47  num_of_sem_filtered_clauses:            0
% 6.16/1.47  num_of_subtypes:                        0
% 6.16/1.47  monotx_restored_types:                  0
% 6.16/1.47  sat_num_of_epr_types:                   0
% 6.16/1.47  sat_num_of_non_cyclic_types:            0
% 6.16/1.47  sat_guarded_non_collapsed_types:        0
% 6.16/1.47  num_pure_diseq_elim:                    0
% 6.16/1.47  simp_replaced_by:                       0
% 6.16/1.47  res_preprocessed:                       22
% 6.16/1.47  prep_upred:                             0
% 6.16/1.47  prep_unflattend:                        0
% 6.16/1.47  smt_new_axioms:                         0
% 6.16/1.47  pred_elim_cands:                        0
% 6.16/1.47  pred_elim:                              0
% 6.16/1.47  pred_elim_cl:                           0
% 6.16/1.47  pred_elim_cycles:                       0
% 6.16/1.47  merged_defs:                            0
% 6.16/1.47  merged_defs_ncl:                        0
% 6.16/1.47  bin_hyper_res:                          0
% 6.16/1.47  prep_cycles:                            2
% 6.16/1.47  pred_elim_time:                         0.
% 6.16/1.47  splitting_time:                         0.
% 6.16/1.47  sem_filter_time:                        0.
% 6.16/1.47  monotx_time:                            0.
% 6.16/1.47  subtype_inf_time:                       0.
% 6.16/1.47  
% 6.16/1.47  ------ Problem properties
% 6.16/1.47  
% 6.16/1.47  clauses:                                9
% 6.16/1.47  conjectures:                            1
% 6.16/1.47  epr:                                    0
% 6.16/1.47  horn:                                   9
% 6.16/1.47  ground:                                 1
% 6.16/1.47  unary:                                  9
% 6.16/1.47  binary:                                 0
% 6.16/1.47  lits:                                   9
% 6.16/1.47  lits_eq:                                9
% 6.16/1.47  fd_pure:                                0
% 6.16/1.47  fd_pseudo:                              0
% 6.16/1.47  fd_cond:                                0
% 6.16/1.47  fd_pseudo_cond:                         0
% 6.16/1.47  ac_symbols:                             1
% 6.16/1.47  
% 6.16/1.47  ------ Propositional Solver
% 6.16/1.47  
% 6.16/1.47  prop_solver_calls:                      13
% 6.16/1.47  prop_fast_solver_calls:                 56
% 6.16/1.47  smt_solver_calls:                       0
% 6.16/1.47  smt_fast_solver_calls:                  0
% 6.16/1.47  prop_num_of_clauses:                    207
% 6.16/1.47  prop_preprocess_simplified:             350
% 6.16/1.47  prop_fo_subsumed:                       0
% 6.16/1.47  prop_solver_time:                       0.
% 6.16/1.47  smt_solver_time:                        0.
% 6.16/1.47  smt_fast_solver_time:                   0.
% 6.16/1.47  prop_fast_solver_time:                  0.
% 6.16/1.47  prop_unsat_core_time:                   0.
% 6.16/1.47  
% 6.16/1.47  ------ QBF
% 6.16/1.47  
% 6.16/1.47  qbf_q_res:                              0
% 6.16/1.47  qbf_num_tautologies:                    0
% 6.16/1.47  qbf_prep_cycles:                        0
% 6.16/1.47  
% 6.16/1.47  ------ BMC1
% 6.16/1.47  
% 6.16/1.47  bmc1_current_bound:                     -1
% 6.16/1.47  bmc1_last_solved_bound:                 -1
% 6.16/1.47  bmc1_unsat_core_size:                   -1
% 6.16/1.47  bmc1_unsat_core_parents_size:           -1
% 6.16/1.47  bmc1_merge_next_fun:                    0
% 6.16/1.47  bmc1_unsat_core_clauses_time:           0.
% 6.16/1.47  
% 6.16/1.47  ------ Instantiation
% 6.16/1.47  
% 6.16/1.47  inst_num_of_clauses:                    0
% 6.16/1.47  inst_num_in_passive:                    0
% 6.16/1.47  inst_num_in_active:                     0
% 6.16/1.47  inst_num_in_unprocessed:                0
% 6.16/1.47  inst_num_of_loops:                      0
% 6.16/1.47  inst_num_of_learning_restarts:          0
% 6.16/1.47  inst_num_moves_active_passive:          0
% 6.16/1.47  inst_lit_activity:                      0
% 6.16/1.47  inst_lit_activity_moves:                0
% 6.16/1.47  inst_num_tautologies:                   0
% 6.16/1.47  inst_num_prop_implied:                  0
% 6.16/1.47  inst_num_existing_simplified:           0
% 6.16/1.47  inst_num_eq_res_simplified:             0
% 6.16/1.47  inst_num_child_elim:                    0
% 6.16/1.47  inst_num_of_dismatching_blockings:      0
% 6.16/1.47  inst_num_of_non_proper_insts:           0
% 6.16/1.47  inst_num_of_duplicates:                 0
% 6.16/1.47  inst_inst_num_from_inst_to_res:         0
% 6.16/1.47  inst_dismatching_checking_time:         0.
% 6.16/1.47  
% 6.16/1.47  ------ Resolution
% 6.16/1.47  
% 6.16/1.47  res_num_of_clauses:                     0
% 6.16/1.47  res_num_in_passive:                     0
% 6.16/1.47  res_num_in_active:                      0
% 6.16/1.47  res_num_of_loops:                       24
% 6.16/1.47  res_forward_subset_subsumed:            0
% 6.16/1.47  res_backward_subset_subsumed:           0
% 6.16/1.47  res_forward_subsumed:                   0
% 6.16/1.47  res_backward_subsumed:                  0
% 6.16/1.47  res_forward_subsumption_resolution:     0
% 6.16/1.47  res_backward_subsumption_resolution:    0
% 6.16/1.47  res_clause_to_clause_subsumption:       46481
% 6.16/1.47  res_orphan_elimination:                 0
% 6.16/1.47  res_tautology_del:                      0
% 6.16/1.47  res_num_eq_res_simplified:              0
% 6.16/1.47  res_num_sel_changes:                    0
% 6.16/1.47  res_moves_from_active_to_pass:          0
% 6.16/1.47  
% 6.16/1.47  ------ Superposition
% 6.16/1.47  
% 6.16/1.47  sup_time_total:                         0.
% 6.16/1.47  sup_time_generating:                    0.
% 6.16/1.47  sup_time_sim_full:                      0.
% 6.16/1.47  sup_time_sim_immed:                     0.
% 6.16/1.47  
% 6.16/1.47  sup_num_of_clauses:                     1689
% 6.16/1.47  sup_num_in_active:                      98
% 6.16/1.47  sup_num_in_passive:                     1591
% 6.16/1.47  sup_num_of_loops:                       124
% 6.16/1.47  sup_fw_superposition:                   7702
% 6.16/1.47  sup_bw_superposition:                   5664
% 6.16/1.47  sup_immediate_simplified:               6541
% 6.16/1.47  sup_given_eliminated:                   0
% 6.16/1.47  comparisons_done:                       0
% 6.16/1.47  comparisons_avoided:                    0
% 6.16/1.47  
% 6.16/1.47  ------ Simplifications
% 6.16/1.47  
% 6.16/1.47  
% 6.16/1.47  sim_fw_subset_subsumed:                 0
% 6.16/1.47  sim_bw_subset_subsumed:                 0
% 6.16/1.47  sim_fw_subsumed:                        1120
% 6.16/1.47  sim_bw_subsumed:                        20
% 6.16/1.47  sim_fw_subsumption_res:                 0
% 6.16/1.47  sim_bw_subsumption_res:                 0
% 6.16/1.47  sim_tautology_del:                      0
% 6.16/1.47  sim_eq_tautology_del:                   1819
% 6.16/1.47  sim_eq_res_simp:                        0
% 6.16/1.47  sim_fw_demodulated:                     4096
% 6.16/1.47  sim_bw_demodulated:                     42
% 6.16/1.47  sim_light_normalised:                   2603
% 6.16/1.47  sim_joinable_taut:                      29
% 6.16/1.47  sim_joinable_simp:                      1
% 6.16/1.47  sim_ac_normalised:                      0
% 6.16/1.47  sim_smt_subsumption:                    0
% 6.16/1.47  
%------------------------------------------------------------------------------
