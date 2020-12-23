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
% DateTime   : Thu Dec  3 11:25:06 EST 2020

% Result     : Theorem 19.65s
% Output     : CNFRefutation 19.65s
% Verified   : 
% Statistics : Number of formulae       :  188 (49112 expanded)
%              Number of clauses        :  158 (18422 expanded)
%              Number of leaves         :   12 (13673 expanded)
%              Depth                    :   38
%              Number of atoms          :  189 (49113 expanded)
%              Number of equality atoms :  188 (49112 expanded)
%              Maximal formula depth    :    5 (   1 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f17,f24,f24])).

fof(f5,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f20,f24])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f25,f24])).

fof(f11,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f13,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f14,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f26,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f30,plain,(
    k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(definition_unfolding,[],[f26,f24,f18,f18])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_27,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3,c_4])).

cnf(c_6,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_103,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_27,c_6])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_108,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_103,c_2])).

cnf(c_239,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_108,c_1])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_5,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_70,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_27,c_5])).

cnf(c_115,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_70])).

cnf(c_7,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_28,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_7,c_5])).

cnf(c_125,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k2_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_70,c_28])).

cnf(c_126,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(demodulation,[status(thm)],[c_125,c_70])).

cnf(c_40,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_4,c_1])).

cnf(c_42,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_40,c_27])).

cnf(c_127,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_126,c_42])).

cnf(c_167,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_115,c_127])).

cnf(c_247,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_239,c_4,c_167])).

cnf(c_552,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_247,c_5])).

cnf(c_8,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_30,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_0,c_8])).

cnf(c_60421,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_552,c_30])).

cnf(c_79,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_27])).

cnf(c_550,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_247,c_79])).

cnf(c_55,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X1,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) ),
    inference(superposition,[status(thm)],[c_28,c_28])).

cnf(c_46,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X2),X1)))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_0,c_28])).

cnf(c_365,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X2),X1))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) ),
    inference(superposition,[status(thm)],[c_46,c_28])).

cnf(c_31,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_48,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[status(thm)],[c_31,c_28])).

cnf(c_59,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_48,c_31])).

cnf(c_687,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_59,c_5])).

cnf(c_694,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_687,c_5])).

cnf(c_695,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_694,c_5,c_28])).

cnf(c_2018,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) ),
    inference(demodulation,[status(thm)],[c_55,c_365,c_695])).

cnf(c_6165,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X1))) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_550,c_2018])).

cnf(c_6194,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_6165,c_108])).

cnf(c_6195,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_6194,c_4,c_552])).

cnf(c_6394,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_6195,c_6195])).

cnf(c_97,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_27,c_6])).

cnf(c_110,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_97,c_31])).

cnf(c_260,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_110,c_1])).

cnf(c_128,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_127,c_70])).

cnf(c_268,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_260,c_4,c_128])).

cnf(c_6649,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_6394,c_268])).

cnf(c_118,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X2),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_6,c_70])).

cnf(c_165,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X2),X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_118,c_5,c_127])).

cnf(c_1039,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_247,c_165])).

cnf(c_1383,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_1039])).

cnf(c_1583,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_1383])).

cnf(c_657,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_59])).

cnf(c_1669,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1583,c_657])).

cnf(c_1711,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X0),k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_1669,c_247])).

cnf(c_1818,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_1711,c_4])).

cnf(c_1882,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_1818,c_0])).

cnf(c_1972,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_110,c_1882])).

cnf(c_10746,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1972])).

cnf(c_28165,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)),X0) = k2_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_6649,c_10746])).

cnf(c_1844,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_1818])).

cnf(c_2332,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))),X2) = X2 ),
    inference(superposition,[status(thm)],[c_5,c_1844])).

cnf(c_2420,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))),X2) = X2 ),
    inference(demodulation,[status(thm)],[c_2332,c_5])).

cnf(c_2421,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))),X2) = X2 ),
    inference(light_normalisation,[status(thm)],[c_2420,c_2018])).

cnf(c_13596,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)),k2_xboole_0(X2,k4_xboole_0(X0,X2))) = k2_xboole_0(X2,k4_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_79,c_2421])).

cnf(c_13835,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k4_xboole_0(X0,X2))) = k2_xboole_0(X2,k4_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_13596,c_2])).

cnf(c_1958,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_1882])).

cnf(c_2435,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k2_xboole_0(X2,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_5,c_1958])).

cnf(c_2516,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X0))))) = X0 ),
    inference(demodulation,[status(thm)],[c_2435,c_5])).

cnf(c_2517,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X0)))) = X0 ),
    inference(demodulation,[status(thm)],[c_2516,c_2018])).

cnf(c_15798,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k2_xboole_0(X2,k1_xboole_0))) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_79,c_2517])).

cnf(c_16033,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X2)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_15798,c_2])).

cnf(c_1714,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_1669,c_5])).

cnf(c_1735,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1714,c_5,c_127])).

cnf(c_2463,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X2),k1_xboole_0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1735,c_1958])).

cnf(c_2491,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X2,k1_xboole_0))) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_2463,c_5])).

cnf(c_2492,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_2491,c_2])).

cnf(c_25290,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),X2),X0) = k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_6649,c_2492])).

cnf(c_257,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_110,c_79])).

cnf(c_93,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X1,X0))) = k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1,c_6])).

cnf(c_27363,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1))),k4_xboole_0(X2,k1_xboole_0)) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_257,c_93])).

cnf(c_1869,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_247,c_1818])).

cnf(c_2522,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1869])).

cnf(c_224,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)))) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) ),
    inference(superposition,[status(thm)],[c_167,c_28])).

cnf(c_227,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_224,c_2,c_55,c_79])).

cnf(c_2744,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2522,c_227])).

cnf(c_16749,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X2,X1)),k1_xboole_0) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_2744,c_268])).

cnf(c_1870,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_268,c_1818])).

cnf(c_2568,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_1870])).

cnf(c_2785,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X0))) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_2568,c_247])).

cnf(c_2817,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_2785,c_167])).

cnf(c_3778,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) = k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_2817,c_6])).

cnf(c_3787,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
    inference(demodulation,[status(thm)],[c_3778,c_2817])).

cnf(c_3788,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_3787,c_4])).

cnf(c_1984,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_268,c_1882])).

cnf(c_15149,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X2,X1)) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
    inference(superposition,[status(thm)],[c_3788,c_1984])).

cnf(c_16793,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),k1_xboole_0) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_16749,c_15149])).

cnf(c_143,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)))) ),
    inference(superposition,[status(thm)],[c_79,c_28])).

cnf(c_148,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X0,X2)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_143,c_2,c_55,c_79])).

cnf(c_1433,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X2,k2_xboole_0(X1,k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1039,c_148])).

cnf(c_1445,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1433,c_2,c_5])).

cnf(c_4856,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1882,c_1445])).

cnf(c_25314,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6649,c_4856])).

cnf(c_27711,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0),k4_xboole_0(X2,k1_xboole_0)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_27363,c_257,c_16793,c_25314])).

cnf(c_2772,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X2,X0),X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_6,c_2568])).

cnf(c_105,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X2,X0),X1) ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_2525,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X2,X0),X1)) = k2_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_6,c_1869])).

cnf(c_2566,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X2,X0),X1)) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
    inference(demodulation,[status(thm)],[c_2525,c_105])).

cnf(c_2822,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X2) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(light_normalisation,[status(thm)],[c_2772,c_105,c_2566])).

cnf(c_19304,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),X3),X2) ),
    inference(superposition,[status(thm)],[c_2822,c_6])).

cnf(c_145,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X1)) = k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_79,c_28])).

cnf(c_146,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X1)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_145,c_2])).

cnf(c_290,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) ),
    inference(superposition,[status(thm)],[c_146,c_28])).

cnf(c_298,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_290,c_79])).

cnf(c_631,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_298,c_5])).

cnf(c_72,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) ),
    inference(superposition,[status(thm)],[c_5,c_5])).

cnf(c_88,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_72,c_5])).

cnf(c_644,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_631,c_88,c_127])).

cnf(c_1858,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_110,c_1818])).

cnf(c_9767,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1858])).

cnf(c_26329,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),X2))) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),X2),X0) ),
    inference(superposition,[status(thm)],[c_644,c_9767])).

cnf(c_8186,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),X2),k4_xboole_0(X0,k1_xboole_0)) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),X2) ),
    inference(superposition,[status(thm)],[c_644,c_1958])).

cnf(c_8232,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),X2),X0) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_8186,c_4])).

cnf(c_8165,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),X2)) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),X2) ),
    inference(superposition,[status(thm)],[c_644,c_1844])).

cnf(c_8246,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),X2)) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_8165,c_4])).

cnf(c_26640,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),X2)) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_26329,c_8232,c_8246])).

cnf(c_9780,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X0,X1)),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1984,c_1858])).

cnf(c_1983,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_247,c_1882])).

cnf(c_2611,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1983])).

cnf(c_9884,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_9780,c_128,c_2611])).

cnf(c_15247,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_3788,c_9884])).

cnf(c_26641,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),X2) = k2_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X1)),X2) ),
    inference(demodulation,[status(thm)],[c_26640,c_15247])).

cnf(c_27712,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_27711,c_4,c_2817,c_19304,c_26641])).

cnf(c_28322,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_28165,c_13835,c_16033,c_25290,c_27712])).

cnf(c_28323,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_28322,c_2568])).

cnf(c_102,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X2,X3)),X1) ),
    inference(superposition,[status(thm)],[c_5,c_6])).

cnf(c_46729,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k2_xboole_0(X2,X1))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X3,X2)),k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_28323,c_102])).

cnf(c_1713,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_1669,c_6])).

cnf(c_1736,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k4_xboole_0(X2,X0) ),
    inference(demodulation,[status(thm)],[c_1713,c_31])).

cnf(c_1720,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X0,k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1669,c_148])).

cnf(c_1733,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1720,c_2])).

cnf(c_2361,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_1733,c_1844])).

cnf(c_2393,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
    inference(demodulation,[status(thm)],[c_2361,c_5])).

cnf(c_2394,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
    inference(demodulation,[status(thm)],[c_2393,c_2])).

cnf(c_13137,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_0,c_2394])).

cnf(c_29664,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(k4_xboole_0(X2,X0),X0) ),
    inference(superposition,[status(thm)],[c_28323,c_13137])).

cnf(c_29742,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_29664,c_13137])).

cnf(c_30208,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k2_xboole_0(k4_xboole_0(X2,X0),X0) ),
    inference(superposition,[status(thm)],[c_1736,c_29742])).

cnf(c_30411,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k2_xboole_0(X2,X0) ),
    inference(demodulation,[status(thm)],[c_30208,c_29742])).

cnf(c_3767,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),k1_xboole_0) = k2_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X2,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_2817,c_6])).

cnf(c_3796,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k1_xboole_0)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_3767,c_2817])).

cnf(c_3797,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
    inference(demodulation,[status(thm)],[c_3796,c_4])).

cnf(c_45201,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_30411,c_3797])).

cnf(c_59238,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X2)),X3)) = k2_xboole_0(k4_xboole_0(X1,X3),X0) ),
    inference(superposition,[status(thm)],[c_102,c_45201])).

cnf(c_60422,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK0),sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_60421,c_46729,c_59238])).

cnf(c_60423,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_60422,c_31,c_1669])).

cnf(c_62638,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1,c_60423])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:04:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 19.65/2.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.65/2.99  
% 19.65/2.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.65/2.99  
% 19.65/2.99  ------  iProver source info
% 19.65/2.99  
% 19.65/2.99  git: date: 2020-06-30 10:37:57 +0100
% 19.65/2.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.65/2.99  git: non_committed_changes: false
% 19.65/2.99  git: last_make_outside_of_git: false
% 19.65/2.99  
% 19.65/2.99  ------ 
% 19.65/2.99  
% 19.65/2.99  ------ Input Options
% 19.65/2.99  
% 19.65/2.99  --out_options                           all
% 19.65/2.99  --tptp_safe_out                         true
% 19.65/2.99  --problem_path                          ""
% 19.65/2.99  --include_path                          ""
% 19.65/2.99  --clausifier                            res/vclausify_rel
% 19.65/2.99  --clausifier_options                    --mode clausify
% 19.65/2.99  --stdin                                 false
% 19.65/2.99  --stats_out                             all
% 19.65/2.99  
% 19.65/2.99  ------ General Options
% 19.65/2.99  
% 19.65/2.99  --fof                                   false
% 19.65/2.99  --time_out_real                         305.
% 19.65/2.99  --time_out_virtual                      -1.
% 19.65/2.99  --symbol_type_check                     false
% 19.65/2.99  --clausify_out                          false
% 19.65/2.99  --sig_cnt_out                           false
% 19.65/2.99  --trig_cnt_out                          false
% 19.65/2.99  --trig_cnt_out_tolerance                1.
% 19.65/2.99  --trig_cnt_out_sk_spl                   false
% 19.65/2.99  --abstr_cl_out                          false
% 19.65/2.99  
% 19.65/2.99  ------ Global Options
% 19.65/2.99  
% 19.65/2.99  --schedule                              default
% 19.65/2.99  --add_important_lit                     false
% 19.65/2.99  --prop_solver_per_cl                    1000
% 19.65/2.99  --min_unsat_core                        false
% 19.65/2.99  --soft_assumptions                      false
% 19.65/2.99  --soft_lemma_size                       3
% 19.65/2.99  --prop_impl_unit_size                   0
% 19.65/2.99  --prop_impl_unit                        []
% 19.65/2.99  --share_sel_clauses                     true
% 19.65/2.99  --reset_solvers                         false
% 19.65/2.99  --bc_imp_inh                            [conj_cone]
% 19.65/2.99  --conj_cone_tolerance                   3.
% 19.65/2.99  --extra_neg_conj                        none
% 19.65/2.99  --large_theory_mode                     true
% 19.65/2.99  --prolific_symb_bound                   200
% 19.65/2.99  --lt_threshold                          2000
% 19.65/2.99  --clause_weak_htbl                      true
% 19.65/2.99  --gc_record_bc_elim                     false
% 19.65/2.99  
% 19.65/2.99  ------ Preprocessing Options
% 19.65/2.99  
% 19.65/2.99  --preprocessing_flag                    true
% 19.65/2.99  --time_out_prep_mult                    0.1
% 19.65/2.99  --splitting_mode                        input
% 19.65/2.99  --splitting_grd                         true
% 19.65/2.99  --splitting_cvd                         false
% 19.65/2.99  --splitting_cvd_svl                     false
% 19.65/2.99  --splitting_nvd                         32
% 19.65/2.99  --sub_typing                            true
% 19.65/2.99  --prep_gs_sim                           true
% 19.65/2.99  --prep_unflatten                        true
% 19.65/2.99  --prep_res_sim                          true
% 19.65/2.99  --prep_upred                            true
% 19.65/2.99  --prep_sem_filter                       exhaustive
% 19.65/2.99  --prep_sem_filter_out                   false
% 19.65/2.99  --pred_elim                             true
% 19.65/2.99  --res_sim_input                         true
% 19.65/2.99  --eq_ax_congr_red                       true
% 19.65/2.99  --pure_diseq_elim                       true
% 19.65/2.99  --brand_transform                       false
% 19.65/2.99  --non_eq_to_eq                          false
% 19.65/2.99  --prep_def_merge                        true
% 19.65/2.99  --prep_def_merge_prop_impl              false
% 19.65/2.99  --prep_def_merge_mbd                    true
% 19.65/2.99  --prep_def_merge_tr_red                 false
% 19.65/2.99  --prep_def_merge_tr_cl                  false
% 19.65/2.99  --smt_preprocessing                     true
% 19.65/2.99  --smt_ac_axioms                         fast
% 19.65/2.99  --preprocessed_out                      false
% 19.65/2.99  --preprocessed_stats                    false
% 19.65/2.99  
% 19.65/2.99  ------ Abstraction refinement Options
% 19.65/2.99  
% 19.65/2.99  --abstr_ref                             []
% 19.65/2.99  --abstr_ref_prep                        false
% 19.65/2.99  --abstr_ref_until_sat                   false
% 19.65/2.99  --abstr_ref_sig_restrict                funpre
% 19.65/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.65/2.99  --abstr_ref_under                       []
% 19.65/2.99  
% 19.65/2.99  ------ SAT Options
% 19.65/2.99  
% 19.65/2.99  --sat_mode                              false
% 19.65/2.99  --sat_fm_restart_options                ""
% 19.65/2.99  --sat_gr_def                            false
% 19.65/2.99  --sat_epr_types                         true
% 19.65/2.99  --sat_non_cyclic_types                  false
% 19.65/2.99  --sat_finite_models                     false
% 19.65/2.99  --sat_fm_lemmas                         false
% 19.65/2.99  --sat_fm_prep                           false
% 19.65/2.99  --sat_fm_uc_incr                        true
% 19.65/2.99  --sat_out_model                         small
% 19.65/2.99  --sat_out_clauses                       false
% 19.65/2.99  
% 19.65/2.99  ------ QBF Options
% 19.65/2.99  
% 19.65/2.99  --qbf_mode                              false
% 19.65/2.99  --qbf_elim_univ                         false
% 19.65/2.99  --qbf_dom_inst                          none
% 19.65/2.99  --qbf_dom_pre_inst                      false
% 19.65/2.99  --qbf_sk_in                             false
% 19.65/2.99  --qbf_pred_elim                         true
% 19.65/2.99  --qbf_split                             512
% 19.65/2.99  
% 19.65/2.99  ------ BMC1 Options
% 19.65/2.99  
% 19.65/2.99  --bmc1_incremental                      false
% 19.65/2.99  --bmc1_axioms                           reachable_all
% 19.65/2.99  --bmc1_min_bound                        0
% 19.65/2.99  --bmc1_max_bound                        -1
% 19.65/2.99  --bmc1_max_bound_default                -1
% 19.65/2.99  --bmc1_symbol_reachability              true
% 19.65/2.99  --bmc1_property_lemmas                  false
% 19.65/2.99  --bmc1_k_induction                      false
% 19.65/2.99  --bmc1_non_equiv_states                 false
% 19.65/2.99  --bmc1_deadlock                         false
% 19.65/2.99  --bmc1_ucm                              false
% 19.65/2.99  --bmc1_add_unsat_core                   none
% 19.65/2.99  --bmc1_unsat_core_children              false
% 19.65/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.65/2.99  --bmc1_out_stat                         full
% 19.65/2.99  --bmc1_ground_init                      false
% 19.65/2.99  --bmc1_pre_inst_next_state              false
% 19.65/2.99  --bmc1_pre_inst_state                   false
% 19.65/2.99  --bmc1_pre_inst_reach_state             false
% 19.65/2.99  --bmc1_out_unsat_core                   false
% 19.65/2.99  --bmc1_aig_witness_out                  false
% 19.65/2.99  --bmc1_verbose                          false
% 19.65/2.99  --bmc1_dump_clauses_tptp                false
% 19.65/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.65/2.99  --bmc1_dump_file                        -
% 19.65/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.65/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.65/2.99  --bmc1_ucm_extend_mode                  1
% 19.65/2.99  --bmc1_ucm_init_mode                    2
% 19.65/2.99  --bmc1_ucm_cone_mode                    none
% 19.65/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.65/2.99  --bmc1_ucm_relax_model                  4
% 19.65/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.65/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.65/2.99  --bmc1_ucm_layered_model                none
% 19.65/2.99  --bmc1_ucm_max_lemma_size               10
% 19.65/2.99  
% 19.65/2.99  ------ AIG Options
% 19.65/2.99  
% 19.65/2.99  --aig_mode                              false
% 19.65/2.99  
% 19.65/2.99  ------ Instantiation Options
% 19.65/2.99  
% 19.65/2.99  --instantiation_flag                    true
% 19.65/2.99  --inst_sos_flag                         false
% 19.65/2.99  --inst_sos_phase                        true
% 19.65/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.65/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.65/2.99  --inst_lit_sel_side                     num_symb
% 19.65/2.99  --inst_solver_per_active                1400
% 19.65/2.99  --inst_solver_calls_frac                1.
% 19.65/2.99  --inst_passive_queue_type               priority_queues
% 19.65/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.65/2.99  --inst_passive_queues_freq              [25;2]
% 19.65/2.99  --inst_dismatching                      true
% 19.65/2.99  --inst_eager_unprocessed_to_passive     true
% 19.65/2.99  --inst_prop_sim_given                   true
% 19.65/2.99  --inst_prop_sim_new                     false
% 19.65/2.99  --inst_subs_new                         false
% 19.65/2.99  --inst_eq_res_simp                      false
% 19.65/2.99  --inst_subs_given                       false
% 19.65/2.99  --inst_orphan_elimination               true
% 19.65/2.99  --inst_learning_loop_flag               true
% 19.65/2.99  --inst_learning_start                   3000
% 19.65/2.99  --inst_learning_factor                  2
% 19.65/2.99  --inst_start_prop_sim_after_learn       3
% 19.65/2.99  --inst_sel_renew                        solver
% 19.65/2.99  --inst_lit_activity_flag                true
% 19.65/2.99  --inst_restr_to_given                   false
% 19.65/2.99  --inst_activity_threshold               500
% 19.65/2.99  --inst_out_proof                        true
% 19.65/2.99  
% 19.65/2.99  ------ Resolution Options
% 19.65/2.99  
% 19.65/2.99  --resolution_flag                       true
% 19.65/2.99  --res_lit_sel                           adaptive
% 19.65/2.99  --res_lit_sel_side                      none
% 19.65/2.99  --res_ordering                          kbo
% 19.65/2.99  --res_to_prop_solver                    active
% 19.65/2.99  --res_prop_simpl_new                    false
% 19.65/2.99  --res_prop_simpl_given                  true
% 19.65/2.99  --res_passive_queue_type                priority_queues
% 19.65/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.65/2.99  --res_passive_queues_freq               [15;5]
% 19.65/2.99  --res_forward_subs                      full
% 19.65/2.99  --res_backward_subs                     full
% 19.65/2.99  --res_forward_subs_resolution           true
% 19.65/2.99  --res_backward_subs_resolution          true
% 19.65/2.99  --res_orphan_elimination                true
% 19.65/2.99  --res_time_limit                        2.
% 19.65/2.99  --res_out_proof                         true
% 19.65/2.99  
% 19.65/2.99  ------ Superposition Options
% 19.65/2.99  
% 19.65/2.99  --superposition_flag                    true
% 19.65/2.99  --sup_passive_queue_type                priority_queues
% 19.65/2.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.65/2.99  --sup_passive_queues_freq               [8;1;4]
% 19.65/2.99  --demod_completeness_check              fast
% 19.65/2.99  --demod_use_ground                      true
% 19.65/2.99  --sup_to_prop_solver                    passive
% 19.65/2.99  --sup_prop_simpl_new                    true
% 19.65/2.99  --sup_prop_simpl_given                  true
% 19.65/2.99  --sup_fun_splitting                     false
% 19.65/2.99  --sup_smt_interval                      50000
% 19.65/2.99  
% 19.65/2.99  ------ Superposition Simplification Setup
% 19.65/2.99  
% 19.65/2.99  --sup_indices_passive                   []
% 19.65/2.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.65/2.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.65/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.65/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.65/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.65/2.99  --sup_full_bw                           [BwDemod]
% 19.65/2.99  --sup_immed_triv                        [TrivRules]
% 19.65/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.65/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.65/2.99  --sup_immed_bw_main                     []
% 19.65/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.65/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.65/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.65/2.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.65/2.99  
% 19.65/2.99  ------ Combination Options
% 19.65/2.99  
% 19.65/2.99  --comb_res_mult                         3
% 19.65/2.99  --comb_sup_mult                         2
% 19.65/2.99  --comb_inst_mult                        10
% 19.65/2.99  
% 19.65/2.99  ------ Debug Options
% 19.65/2.99  
% 19.65/2.99  --dbg_backtrace                         false
% 19.65/2.99  --dbg_dump_prop_clauses                 false
% 19.65/2.99  --dbg_dump_prop_clauses_file            -
% 19.65/2.99  --dbg_out_stat                          false
% 19.65/2.99  ------ Parsing...
% 19.65/2.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.65/2.99  
% 19.65/2.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 19.65/2.99  
% 19.65/2.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.65/2.99  
% 19.65/2.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.65/2.99  ------ Proving...
% 19.65/2.99  ------ Problem Properties 
% 19.65/2.99  
% 19.65/2.99  
% 19.65/2.99  clauses                                 9
% 19.65/2.99  conjectures                             1
% 19.65/2.99  EPR                                     0
% 19.65/2.99  Horn                                    9
% 19.65/2.99  unary                                   9
% 19.65/2.99  binary                                  0
% 19.65/2.99  lits                                    9
% 19.65/2.99  lits eq                                 9
% 19.65/2.99  fd_pure                                 0
% 19.65/2.99  fd_pseudo                               0
% 19.65/2.99  fd_cond                                 0
% 19.65/2.99  fd_pseudo_cond                          0
% 19.65/2.99  AC symbols                              0
% 19.65/2.99  
% 19.65/2.99  ------ Schedule UEQ
% 19.65/2.99  
% 19.65/2.99  ------ pure equality problem: resolution off 
% 19.65/2.99  
% 19.65/2.99  ------ Option_UEQ Time Limit: Unbounded
% 19.65/2.99  
% 19.65/2.99  
% 19.65/2.99  ------ 
% 19.65/2.99  Current options:
% 19.65/2.99  ------ 
% 19.65/2.99  
% 19.65/2.99  ------ Input Options
% 19.65/2.99  
% 19.65/2.99  --out_options                           all
% 19.65/2.99  --tptp_safe_out                         true
% 19.65/2.99  --problem_path                          ""
% 19.65/2.99  --include_path                          ""
% 19.65/2.99  --clausifier                            res/vclausify_rel
% 19.65/2.99  --clausifier_options                    --mode clausify
% 19.65/2.99  --stdin                                 false
% 19.65/2.99  --stats_out                             all
% 19.65/2.99  
% 19.65/2.99  ------ General Options
% 19.65/2.99  
% 19.65/2.99  --fof                                   false
% 19.65/2.99  --time_out_real                         305.
% 19.65/2.99  --time_out_virtual                      -1.
% 19.65/2.99  --symbol_type_check                     false
% 19.65/2.99  --clausify_out                          false
% 19.65/2.99  --sig_cnt_out                           false
% 19.65/2.99  --trig_cnt_out                          false
% 19.65/2.99  --trig_cnt_out_tolerance                1.
% 19.65/2.99  --trig_cnt_out_sk_spl                   false
% 19.65/2.99  --abstr_cl_out                          false
% 19.65/2.99  
% 19.65/2.99  ------ Global Options
% 19.65/2.99  
% 19.65/2.99  --schedule                              default
% 19.65/2.99  --add_important_lit                     false
% 19.65/2.99  --prop_solver_per_cl                    1000
% 19.65/2.99  --min_unsat_core                        false
% 19.65/2.99  --soft_assumptions                      false
% 19.65/2.99  --soft_lemma_size                       3
% 19.65/2.99  --prop_impl_unit_size                   0
% 19.65/2.99  --prop_impl_unit                        []
% 19.65/2.99  --share_sel_clauses                     true
% 19.65/2.99  --reset_solvers                         false
% 19.65/2.99  --bc_imp_inh                            [conj_cone]
% 19.65/2.99  --conj_cone_tolerance                   3.
% 19.65/2.99  --extra_neg_conj                        none
% 19.65/2.99  --large_theory_mode                     true
% 19.65/2.99  --prolific_symb_bound                   200
% 19.65/2.99  --lt_threshold                          2000
% 19.65/2.99  --clause_weak_htbl                      true
% 19.65/2.99  --gc_record_bc_elim                     false
% 19.65/2.99  
% 19.65/2.99  ------ Preprocessing Options
% 19.65/2.99  
% 19.65/2.99  --preprocessing_flag                    true
% 19.65/2.99  --time_out_prep_mult                    0.1
% 19.65/2.99  --splitting_mode                        input
% 19.65/2.99  --splitting_grd                         true
% 19.65/2.99  --splitting_cvd                         false
% 19.65/2.99  --splitting_cvd_svl                     false
% 19.65/2.99  --splitting_nvd                         32
% 19.65/2.99  --sub_typing                            true
% 19.65/2.99  --prep_gs_sim                           true
% 19.65/2.99  --prep_unflatten                        true
% 19.65/2.99  --prep_res_sim                          true
% 19.65/2.99  --prep_upred                            true
% 19.65/2.99  --prep_sem_filter                       exhaustive
% 19.65/2.99  --prep_sem_filter_out                   false
% 19.65/2.99  --pred_elim                             true
% 19.65/2.99  --res_sim_input                         true
% 19.65/2.99  --eq_ax_congr_red                       true
% 19.65/2.99  --pure_diseq_elim                       true
% 19.65/2.99  --brand_transform                       false
% 19.65/2.99  --non_eq_to_eq                          false
% 19.65/2.99  --prep_def_merge                        true
% 19.65/2.99  --prep_def_merge_prop_impl              false
% 19.65/2.99  --prep_def_merge_mbd                    true
% 19.65/2.99  --prep_def_merge_tr_red                 false
% 19.65/2.99  --prep_def_merge_tr_cl                  false
% 19.65/2.99  --smt_preprocessing                     true
% 19.65/2.99  --smt_ac_axioms                         fast
% 19.65/2.99  --preprocessed_out                      false
% 19.65/2.99  --preprocessed_stats                    false
% 19.65/2.99  
% 19.65/2.99  ------ Abstraction refinement Options
% 19.65/2.99  
% 19.65/2.99  --abstr_ref                             []
% 19.65/2.99  --abstr_ref_prep                        false
% 19.65/2.99  --abstr_ref_until_sat                   false
% 19.65/2.99  --abstr_ref_sig_restrict                funpre
% 19.65/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.65/2.99  --abstr_ref_under                       []
% 19.65/2.99  
% 19.65/2.99  ------ SAT Options
% 19.65/2.99  
% 19.65/2.99  --sat_mode                              false
% 19.65/2.99  --sat_fm_restart_options                ""
% 19.65/2.99  --sat_gr_def                            false
% 19.65/2.99  --sat_epr_types                         true
% 19.65/2.99  --sat_non_cyclic_types                  false
% 19.65/2.99  --sat_finite_models                     false
% 19.65/2.99  --sat_fm_lemmas                         false
% 19.65/2.99  --sat_fm_prep                           false
% 19.65/2.99  --sat_fm_uc_incr                        true
% 19.65/2.99  --sat_out_model                         small
% 19.65/2.99  --sat_out_clauses                       false
% 19.65/2.99  
% 19.65/2.99  ------ QBF Options
% 19.65/2.99  
% 19.65/2.99  --qbf_mode                              false
% 19.65/2.99  --qbf_elim_univ                         false
% 19.65/2.99  --qbf_dom_inst                          none
% 19.65/2.99  --qbf_dom_pre_inst                      false
% 19.65/2.99  --qbf_sk_in                             false
% 19.65/2.99  --qbf_pred_elim                         true
% 19.65/2.99  --qbf_split                             512
% 19.65/2.99  
% 19.65/2.99  ------ BMC1 Options
% 19.65/2.99  
% 19.65/2.99  --bmc1_incremental                      false
% 19.65/2.99  --bmc1_axioms                           reachable_all
% 19.65/2.99  --bmc1_min_bound                        0
% 19.65/2.99  --bmc1_max_bound                        -1
% 19.65/2.99  --bmc1_max_bound_default                -1
% 19.65/2.99  --bmc1_symbol_reachability              true
% 19.65/2.99  --bmc1_property_lemmas                  false
% 19.65/2.99  --bmc1_k_induction                      false
% 19.65/2.99  --bmc1_non_equiv_states                 false
% 19.65/2.99  --bmc1_deadlock                         false
% 19.65/2.99  --bmc1_ucm                              false
% 19.65/2.99  --bmc1_add_unsat_core                   none
% 19.65/2.99  --bmc1_unsat_core_children              false
% 19.65/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.65/2.99  --bmc1_out_stat                         full
% 19.65/2.99  --bmc1_ground_init                      false
% 19.65/2.99  --bmc1_pre_inst_next_state              false
% 19.65/2.99  --bmc1_pre_inst_state                   false
% 19.65/2.99  --bmc1_pre_inst_reach_state             false
% 19.65/2.99  --bmc1_out_unsat_core                   false
% 19.65/2.99  --bmc1_aig_witness_out                  false
% 19.65/2.99  --bmc1_verbose                          false
% 19.65/2.99  --bmc1_dump_clauses_tptp                false
% 19.65/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.65/2.99  --bmc1_dump_file                        -
% 19.65/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.65/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.65/2.99  --bmc1_ucm_extend_mode                  1
% 19.65/2.99  --bmc1_ucm_init_mode                    2
% 19.65/2.99  --bmc1_ucm_cone_mode                    none
% 19.65/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.65/2.99  --bmc1_ucm_relax_model                  4
% 19.65/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.65/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.65/2.99  --bmc1_ucm_layered_model                none
% 19.65/2.99  --bmc1_ucm_max_lemma_size               10
% 19.65/2.99  
% 19.65/2.99  ------ AIG Options
% 19.65/2.99  
% 19.65/2.99  --aig_mode                              false
% 19.65/2.99  
% 19.65/2.99  ------ Instantiation Options
% 19.65/2.99  
% 19.65/2.99  --instantiation_flag                    false
% 19.65/2.99  --inst_sos_flag                         false
% 19.65/2.99  --inst_sos_phase                        true
% 19.65/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.65/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.65/2.99  --inst_lit_sel_side                     num_symb
% 19.65/2.99  --inst_solver_per_active                1400
% 19.65/2.99  --inst_solver_calls_frac                1.
% 19.65/2.99  --inst_passive_queue_type               priority_queues
% 19.65/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.65/2.99  --inst_passive_queues_freq              [25;2]
% 19.65/2.99  --inst_dismatching                      true
% 19.65/2.99  --inst_eager_unprocessed_to_passive     true
% 19.65/2.99  --inst_prop_sim_given                   true
% 19.65/2.99  --inst_prop_sim_new                     false
% 19.65/2.99  --inst_subs_new                         false
% 19.65/2.99  --inst_eq_res_simp                      false
% 19.65/2.99  --inst_subs_given                       false
% 19.65/2.99  --inst_orphan_elimination               true
% 19.65/2.99  --inst_learning_loop_flag               true
% 19.65/2.99  --inst_learning_start                   3000
% 19.65/2.99  --inst_learning_factor                  2
% 19.65/2.99  --inst_start_prop_sim_after_learn       3
% 19.65/2.99  --inst_sel_renew                        solver
% 19.65/2.99  --inst_lit_activity_flag                true
% 19.65/2.99  --inst_restr_to_given                   false
% 19.65/2.99  --inst_activity_threshold               500
% 19.65/2.99  --inst_out_proof                        true
% 19.65/2.99  
% 19.65/2.99  ------ Resolution Options
% 19.65/2.99  
% 19.65/2.99  --resolution_flag                       false
% 19.65/2.99  --res_lit_sel                           adaptive
% 19.65/2.99  --res_lit_sel_side                      none
% 19.65/2.99  --res_ordering                          kbo
% 19.65/2.99  --res_to_prop_solver                    active
% 19.65/2.99  --res_prop_simpl_new                    false
% 19.65/2.99  --res_prop_simpl_given                  true
% 19.65/2.99  --res_passive_queue_type                priority_queues
% 19.65/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.65/2.99  --res_passive_queues_freq               [15;5]
% 19.65/2.99  --res_forward_subs                      full
% 19.65/2.99  --res_backward_subs                     full
% 19.65/2.99  --res_forward_subs_resolution           true
% 19.65/2.99  --res_backward_subs_resolution          true
% 19.65/2.99  --res_orphan_elimination                true
% 19.65/2.99  --res_time_limit                        2.
% 19.65/2.99  --res_out_proof                         true
% 19.65/2.99  
% 19.65/2.99  ------ Superposition Options
% 19.65/2.99  
% 19.65/2.99  --superposition_flag                    true
% 19.65/2.99  --sup_passive_queue_type                priority_queues
% 19.65/2.99  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.65/2.99  --sup_passive_queues_freq               [8;1;4]
% 19.65/2.99  --demod_completeness_check              fast
% 19.65/2.99  --demod_use_ground                      true
% 19.65/2.99  --sup_to_prop_solver                    active
% 19.65/2.99  --sup_prop_simpl_new                    false
% 19.65/2.99  --sup_prop_simpl_given                  false
% 19.65/2.99  --sup_fun_splitting                     true
% 19.65/2.99  --sup_smt_interval                      10000
% 19.65/2.99  
% 19.65/2.99  ------ Superposition Simplification Setup
% 19.65/2.99  
% 19.65/2.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.65/2.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.65/2.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.65/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.65/2.99  --sup_full_triv                         [TrivRules]
% 19.65/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.65/2.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.65/2.99  --sup_immed_triv                        [TrivRules]
% 19.65/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.65/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.65/2.99  --sup_immed_bw_main                     []
% 19.65/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.65/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.65/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.65/2.99  --sup_input_bw                          [BwDemod;BwSubsumption]
% 19.65/2.99  
% 19.65/2.99  ------ Combination Options
% 19.65/2.99  
% 19.65/2.99  --comb_res_mult                         1
% 19.65/2.99  --comb_sup_mult                         1
% 19.65/2.99  --comb_inst_mult                        1000000
% 19.65/2.99  
% 19.65/2.99  ------ Debug Options
% 19.65/2.99  
% 19.65/2.99  --dbg_backtrace                         false
% 19.65/2.99  --dbg_dump_prop_clauses                 false
% 19.65/2.99  --dbg_dump_prop_clauses_file            -
% 19.65/2.99  --dbg_out_stat                          false
% 19.65/2.99  
% 19.65/2.99  
% 19.65/2.99  
% 19.65/2.99  
% 19.65/2.99  ------ Proving...
% 19.65/2.99  
% 19.65/2.99  
% 19.65/2.99  % SZS status Theorem for theBenchmark.p
% 19.65/2.99  
% 19.65/2.99   Resolution empty clause
% 19.65/2.99  
% 19.65/2.99  % SZS output start CNFRefutation for theBenchmark.p
% 19.65/2.99  
% 19.65/2.99  fof(f2,axiom,(
% 19.65/2.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 19.65/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.65/2.99  
% 19.65/2.99  fof(f17,plain,(
% 19.65/2.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 19.65/2.99    inference(cnf_transformation,[],[f2])).
% 19.65/2.99  
% 19.65/2.99  fof(f9,axiom,(
% 19.65/2.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 19.65/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.65/2.99  
% 19.65/2.99  fof(f24,plain,(
% 19.65/2.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 19.65/2.99    inference(cnf_transformation,[],[f9])).
% 19.65/2.99  
% 19.65/2.99  fof(f27,plain,(
% 19.65/2.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 19.65/2.99    inference(definition_unfolding,[],[f17,f24,f24])).
% 19.65/2.99  
% 19.65/2.99  fof(f5,axiom,(
% 19.65/2.99    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 19.65/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.65/2.99  
% 19.65/2.99  fof(f20,plain,(
% 19.65/2.99    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 19.65/2.99    inference(cnf_transformation,[],[f5])).
% 19.65/2.99  
% 19.65/2.99  fof(f28,plain,(
% 19.65/2.99    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 19.65/2.99    inference(definition_unfolding,[],[f20,f24])).
% 19.65/2.99  
% 19.65/2.99  fof(f6,axiom,(
% 19.65/2.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 19.65/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.65/2.99  
% 19.65/2.99  fof(f21,plain,(
% 19.65/2.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 19.65/2.99    inference(cnf_transformation,[],[f6])).
% 19.65/2.99  
% 19.65/2.99  fof(f8,axiom,(
% 19.65/2.99    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2)),
% 19.65/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.65/2.99  
% 19.65/2.99  fof(f23,plain,(
% 19.65/2.99    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 19.65/2.99    inference(cnf_transformation,[],[f8])).
% 19.65/2.99  
% 19.65/2.99  fof(f4,axiom,(
% 19.65/2.99    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 19.65/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.65/2.99  
% 19.65/2.99  fof(f19,plain,(
% 19.65/2.99    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 19.65/2.99    inference(cnf_transformation,[],[f4])).
% 19.65/2.99  
% 19.65/2.99  fof(f1,axiom,(
% 19.65/2.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 19.65/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.65/2.99  
% 19.65/2.99  fof(f16,plain,(
% 19.65/2.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 19.65/2.99    inference(cnf_transformation,[],[f1])).
% 19.65/2.99  
% 19.65/2.99  fof(f7,axiom,(
% 19.65/2.99    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 19.65/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.65/2.99  
% 19.65/2.99  fof(f22,plain,(
% 19.65/2.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 19.65/2.99    inference(cnf_transformation,[],[f7])).
% 19.65/2.99  
% 19.65/2.99  fof(f10,axiom,(
% 19.65/2.99    ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 19.65/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.65/2.99  
% 19.65/2.99  fof(f25,plain,(
% 19.65/2.99    ( ! [X2,X0,X1] : (k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 19.65/2.99    inference(cnf_transformation,[],[f10])).
% 19.65/2.99  
% 19.65/2.99  fof(f29,plain,(
% 19.65/2.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)))) )),
% 19.65/2.99    inference(definition_unfolding,[],[f25,f24])).
% 19.65/2.99  
% 19.65/2.99  fof(f11,conjecture,(
% 19.65/2.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 19.65/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.65/2.99  
% 19.65/2.99  fof(f12,negated_conjecture,(
% 19.65/2.99    ~! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 19.65/2.99    inference(negated_conjecture,[],[f11])).
% 19.65/2.99  
% 19.65/2.99  fof(f13,plain,(
% 19.65/2.99    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 19.65/2.99    inference(ennf_transformation,[],[f12])).
% 19.65/2.99  
% 19.65/2.99  fof(f14,plain,(
% 19.65/2.99    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 19.65/2.99    introduced(choice_axiom,[])).
% 19.65/2.99  
% 19.65/2.99  fof(f15,plain,(
% 19.65/2.99    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 19.65/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 19.65/2.99  
% 19.65/2.99  fof(f26,plain,(
% 19.65/2.99    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 19.65/2.99    inference(cnf_transformation,[],[f15])).
% 19.65/2.99  
% 19.65/2.99  fof(f3,axiom,(
% 19.65/2.99    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 19.65/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.65/2.99  
% 19.65/2.99  fof(f18,plain,(
% 19.65/2.99    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 19.65/2.99    inference(cnf_transformation,[],[f3])).
% 19.65/2.99  
% 19.65/2.99  fof(f30,plain,(
% 19.65/2.99    k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 19.65/2.99    inference(definition_unfolding,[],[f26,f24,f18,f18])).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1,plain,
% 19.65/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 19.65/2.99      inference(cnf_transformation,[],[f27]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_3,plain,
% 19.65/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 19.65/2.99      inference(cnf_transformation,[],[f28]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_4,plain,
% 19.65/2.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 19.65/2.99      inference(cnf_transformation,[],[f21]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_27,plain,
% 19.65/2.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 19.65/2.99      inference(light_normalisation,[status(thm)],[c_3,c_4]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_6,plain,
% 19.65/2.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
% 19.65/2.99      inference(cnf_transformation,[],[f23]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_103,plain,
% 19.65/2.99      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_27,c_6]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2,plain,
% 19.65/2.99      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 19.65/2.99      inference(cnf_transformation,[],[f19]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_108,plain,
% 19.65/2.99      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_103,c_2]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_239,plain,
% 19.65/2.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1))) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_108,c_1]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_0,plain,
% 19.65/2.99      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 19.65/2.99      inference(cnf_transformation,[],[f16]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_5,plain,
% 19.65/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 19.65/2.99      inference(cnf_transformation,[],[f22]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_70,plain,
% 19.65/2.99      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_27,c_5]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_115,plain,
% 19.65/2.99      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k4_xboole_0(k1_xboole_0,X1) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_0,c_70]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_7,plain,
% 19.65/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 19.65/2.99      inference(cnf_transformation,[],[f29]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_28,plain,
% 19.65/2.99      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_7,c_5]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_125,plain,
% 19.65/2.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k2_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_70,c_28]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_126,plain,
% 19.65/2.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) = k4_xboole_0(k1_xboole_0,X1) ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_125,c_70]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_40,plain,
% 19.65/2.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_4,c_1]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_42,plain,
% 19.65/2.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 19.65/2.99      inference(light_normalisation,[status(thm)],[c_40,c_27]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_127,plain,
% 19.65/2.99      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_126,c_42]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_167,plain,
% 19.65/2.99      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_115,c_127]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_247,plain,
% 19.65/2.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_239,c_4,c_167]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_552,plain,
% 19.65/2.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,X2) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_247,c_5]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_8,negated_conjecture,
% 19.65/2.99      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 19.65/2.99      inference(cnf_transformation,[],[f30]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_30,plain,
% 19.65/2.99      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_0,c_8]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_60421,plain,
% 19.65/2.99      ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_552,c_30]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_79,plain,
% 19.65/2.99      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_5,c_27]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_550,plain,
% 19.65/2.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_247,c_79]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_55,plain,
% 19.65/2.99      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X1,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_28,c_28]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_46,plain,
% 19.65/2.99      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X2),X1)))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_0,c_28]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_365,plain,
% 19.65/2.99      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X2),X1))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_46,c_28]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_31,plain,
% 19.65/2.99      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_48,plain,
% 19.65/2.99      ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_31,c_28]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_59,plain,
% 19.65/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_48,c_31]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_687,plain,
% 19.65/2.99      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_59,c_5]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_694,plain,
% 19.65/2.99      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 19.65/2.99      inference(light_normalisation,[status(thm)],[c_687,c_5]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_695,plain,
% 19.65/2.99      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_694,c_5,c_28]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2018,plain,
% 19.65/2.99      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_55,c_365,c_695]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_6165,plain,
% 19.65/2.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X1))) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_550,c_2018]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_6194,plain,
% 19.65/2.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) ),
% 19.65/2.99      inference(light_normalisation,[status(thm)],[c_6165,c_108]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_6195,plain,
% 19.65/2.99      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_6194,c_4,c_552]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_6394,plain,
% 19.65/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_6195,c_6195]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_97,plain,
% 19.65/2.99      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X0)) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_27,c_6]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_110,plain,
% 19.65/2.99      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_97,c_31]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_260,plain,
% 19.65/2.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_110,c_1]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_128,plain,
% 19.65/2.99      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_127,c_70]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_268,plain,
% 19.65/2.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
% 19.65/2.99      inference(light_normalisation,[status(thm)],[c_260,c_4,c_128]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_6649,plain,
% 19.65/2.99      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = X0 ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_6394,c_268]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_118,plain,
% 19.65/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X2),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,X1)) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_6,c_70]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_165,plain,
% 19.65/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X2),X1)) = k1_xboole_0 ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_118,c_5,c_127]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1039,plain,
% 19.65/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_247,c_165]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1383,plain,
% 19.65/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k1_xboole_0 ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_1,c_1039]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1583,plain,
% 19.65/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),X0) = k1_xboole_0 ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_1,c_1383]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_657,plain,
% 19.65/2.99      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_1,c_59]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1669,plain,
% 19.65/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 19.65/2.99      inference(light_normalisation,[status(thm)],[c_1583,c_657]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1711,plain,
% 19.65/2.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X0),k1_xboole_0) = X0 ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_1669,c_247]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1818,plain,
% 19.65/2.99      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_1711,c_4]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1882,plain,
% 19.65/2.99      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_1818,c_0]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1972,plain,
% 19.65/2.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_110,c_1882]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_10746,plain,
% 19.65/2.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_0,c_1972]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_28165,plain,
% 19.65/2.99      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)),X0) = k2_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(X0,k4_xboole_0(X1,X0))) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_6649,c_10746]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1844,plain,
% 19.65/2.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_1,c_1818]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2332,plain,
% 19.65/2.99      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))),X2) = X2 ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_5,c_1844]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2420,plain,
% 19.65/2.99      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))),X2) = X2 ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_2332,c_5]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2421,plain,
% 19.65/2.99      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))),X2) = X2 ),
% 19.65/2.99      inference(light_normalisation,[status(thm)],[c_2420,c_2018]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_13596,plain,
% 19.65/2.99      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)),k2_xboole_0(X2,k4_xboole_0(X0,X2))) = k2_xboole_0(X2,k4_xboole_0(X0,X2)) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_79,c_2421]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_13835,plain,
% 19.65/2.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k4_xboole_0(X0,X2))) = k2_xboole_0(X2,k4_xboole_0(X0,X2)) ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_13596,c_2]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1958,plain,
% 19.65/2.99      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_1,c_1882]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2435,plain,
% 19.65/2.99      ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k2_xboole_0(X2,X0)))) = X0 ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_5,c_1958]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2516,plain,
% 19.65/2.99      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X0))))) = X0 ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_2435,c_5]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2517,plain,
% 19.65/2.99      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X0)))) = X0 ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_2516,c_2018]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_15798,plain,
% 19.65/2.99      ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k2_xboole_0(X2,k1_xboole_0))) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_79,c_2517]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_16033,plain,
% 19.65/2.99      ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X2)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_15798,c_2]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1714,plain,
% 19.65/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_1669,c_5]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1735,plain,
% 19.65/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_1714,c_5,c_127]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2463,plain,
% 19.65/2.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X2),k1_xboole_0)) = k2_xboole_0(X0,X1) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_1735,c_1958]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2491,plain,
% 19.65/2.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X2,k1_xboole_0))) = k2_xboole_0(X0,X1) ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_2463,c_5]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2492,plain,
% 19.65/2.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k2_xboole_0(X0,X1) ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_2491,c_2]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_25290,plain,
% 19.65/2.99      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),X2),X0) = k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),X2) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_6649,c_2492]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_257,plain,
% 19.65/2.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_110,c_79]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_93,plain,
% 19.65/2.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X1,X0))) = k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X0)) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_1,c_6]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_27363,plain,
% 19.65/2.99      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1))),k4_xboole_0(X2,k1_xboole_0)) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_257,c_93]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1869,plain,
% 19.65/2.99      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_247,c_1818]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2522,plain,
% 19.65/2.99      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_0,c_1869]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_224,plain,
% 19.65/2.99      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)))) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_167,c_28]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_227,plain,
% 19.65/2.99      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k1_xboole_0 ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_224,c_2,c_55,c_79]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2744,plain,
% 19.65/2.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X1,X0))) = k1_xboole_0 ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_2522,c_227]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_16749,plain,
% 19.65/2.99      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X2,X1)),k1_xboole_0) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_2744,c_268]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1870,plain,
% 19.65/2.99      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_268,c_1818]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2568,plain,
% 19.65/2.99      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_0,c_1870]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2785,plain,
% 19.65/2.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X0))) = k2_xboole_0(X1,X0) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_2568,c_247]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2817,plain,
% 19.65/2.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 19.65/2.99      inference(light_normalisation,[status(thm)],[c_2785,c_167]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_3778,plain,
% 19.65/2.99      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) = k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X2,X1)) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_2817,c_6]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_3787,plain,
% 19.65/2.99      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_3778,c_2817]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_3788,plain,
% 19.65/2.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 19.65/2.99      inference(light_normalisation,[status(thm)],[c_3787,c_4]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1984,plain,
% 19.65/2.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_268,c_1882]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_15149,plain,
% 19.65/2.99      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X2,X1)) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_3788,c_1984]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_16793,plain,
% 19.65/2.99      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),k1_xboole_0) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 19.65/2.99      inference(light_normalisation,[status(thm)],[c_16749,c_15149]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_143,plain,
% 19.65/2.99      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)))) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_79,c_28]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_148,plain,
% 19.65/2.99      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X0,X2)))) = k1_xboole_0 ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_143,c_2,c_55,c_79]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1433,plain,
% 19.65/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X2,k2_xboole_0(X1,k1_xboole_0))) = k1_xboole_0 ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_1039,c_148]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1445,plain,
% 19.65/2.99      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X1))) = k1_xboole_0 ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_1433,c_2,c_5]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_4856,plain,
% 19.65/2.99      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1)) = k1_xboole_0 ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_1882,c_1445]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_25314,plain,
% 19.65/2.99      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_6649,c_4856]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_27711,plain,
% 19.65/2.99      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0),k4_xboole_0(X2,k1_xboole_0)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 19.65/2.99      inference(light_normalisation,
% 19.65/2.99                [status(thm)],
% 19.65/2.99                [c_27363,c_257,c_16793,c_25314]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2772,plain,
% 19.65/2.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X2,X0),X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_6,c_2568]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_105,plain,
% 19.65/2.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X2,X0),X1) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2525,plain,
% 19.65/2.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X2,X0),X1)) = k2_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X0,X1)) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_6,c_1869]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2566,plain,
% 19.65/2.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X2,X0),X1)) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_2525,c_105]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2822,plain,
% 19.65/2.99      ( k4_xboole_0(k2_xboole_0(X0,X1),X2) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 19.65/2.99      inference(light_normalisation,[status(thm)],[c_2772,c_105,c_2566]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_19304,plain,
% 19.65/2.99      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),X3),X2) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_2822,c_6]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_145,plain,
% 19.65/2.99      ( k4_xboole_0(X0,k2_xboole_0(X1,X1)) = k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_79,c_28]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_146,plain,
% 19.65/2.99      ( k4_xboole_0(X0,k2_xboole_0(X1,X1)) = k4_xboole_0(X0,X1) ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_145,c_2]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_290,plain,
% 19.65/2.99      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_146,c_28]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_298,plain,
% 19.65/2.99      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_290,c_79]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_631,plain,
% 19.65/2.99      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_298,c_5]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_72,plain,
% 19.65/2.99      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_5,c_5]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_88,plain,
% 19.65/2.99      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_72,c_5]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_644,plain,
% 19.65/2.99      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),X2)) = k1_xboole_0 ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_631,c_88,c_127]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1858,plain,
% 19.65/2.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_110,c_1818]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_9767,plain,
% 19.65/2.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_0,c_1858]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_26329,plain,
% 19.65/2.99      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),X2))) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),X2),X0) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_644,c_9767]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_8186,plain,
% 19.65/2.99      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),X2),k4_xboole_0(X0,k1_xboole_0)) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),X2) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_644,c_1958]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_8232,plain,
% 19.65/2.99      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),X2),X0) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),X2) ),
% 19.65/2.99      inference(light_normalisation,[status(thm)],[c_8186,c_4]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_8165,plain,
% 19.65/2.99      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),X2)) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),X2) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_644,c_1844]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_8246,plain,
% 19.65/2.99      ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),X2)) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),X2) ),
% 19.65/2.99      inference(light_normalisation,[status(thm)],[c_8165,c_4]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_26640,plain,
% 19.65/2.99      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),X2)) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),X2) ),
% 19.65/2.99      inference(light_normalisation,[status(thm)],[c_26329,c_8232,c_8246]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_9780,plain,
% 19.65/2.99      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X0,X1)),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_1984,c_1858]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1983,plain,
% 19.65/2.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_247,c_1882]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2611,plain,
% 19.65/2.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_0,c_1983]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_9884,plain,
% 19.65/2.99      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 19.65/2.99      inference(light_normalisation,[status(thm)],[c_9780,c_128,c_2611]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_15247,plain,
% 19.65/2.99      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_3788,c_9884]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_26641,plain,
% 19.65/2.99      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),X2) = k2_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X1)),X2) ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_26640,c_15247]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_27712,plain,
% 19.65/2.99      ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 19.65/2.99      inference(demodulation,
% 19.65/2.99                [status(thm)],
% 19.65/2.99                [c_27711,c_4,c_2817,c_19304,c_26641]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_28322,plain,
% 19.65/2.99      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 19.65/2.99      inference(demodulation,
% 19.65/2.99                [status(thm)],
% 19.65/2.99                [c_28165,c_13835,c_16033,c_25290,c_27712]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_28323,plain,
% 19.65/2.99      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 19.65/2.99      inference(light_normalisation,[status(thm)],[c_28322,c_2568]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_102,plain,
% 19.65/2.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X2,X3)),X1) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_5,c_6]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_46729,plain,
% 19.65/2.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k2_xboole_0(X2,X1))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X3,X2)),k4_xboole_0(X1,X2)) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_28323,c_102]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1713,plain,
% 19.65/2.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,X0)) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_1669,c_6]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1736,plain,
% 19.65/2.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k4_xboole_0(X2,X0) ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_1713,c_31]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1720,plain,
% 19.65/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X0,k1_xboole_0))) = k1_xboole_0 ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_1669,c_148]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1733,plain,
% 19.65/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
% 19.65/2.99      inference(light_normalisation,[status(thm)],[c_1720,c_2]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2361,plain,
% 19.65/2.99      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_1733,c_1844]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2393,plain,
% 19.65/2.99      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_2361,c_5]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2394,plain,
% 19.65/2.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_2393,c_2]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_13137,plain,
% 19.65/2.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X2,X0) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_0,c_2394]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_29664,plain,
% 19.65/2.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(k4_xboole_0(X2,X0),X0) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_28323,c_13137]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_29742,plain,
% 19.65/2.99      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 19.65/2.99      inference(light_normalisation,[status(thm)],[c_29664,c_13137]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_30208,plain,
% 19.65/2.99      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k2_xboole_0(k4_xboole_0(X2,X0),X0) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_1736,c_29742]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_30411,plain,
% 19.65/2.99      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k2_xboole_0(X2,X0) ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_30208,c_29742]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_3767,plain,
% 19.65/2.99      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),k1_xboole_0) = k2_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X2,k1_xboole_0)) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_2817,c_6]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_3796,plain,
% 19.65/2.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k1_xboole_0)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_3767,c_2817]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_3797,plain,
% 19.65/2.99      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_3796,c_4]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_45201,plain,
% 19.65/2.99      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X1,X0) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_30411,c_3797]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_59238,plain,
% 19.65/2.99      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X2)),X3)) = k2_xboole_0(k4_xboole_0(X1,X3),X0) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_102,c_45201]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_60422,plain,
% 19.65/2.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK0),sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_60421,c_46729,c_59238]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_60423,plain,
% 19.65/2.99      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_60422,c_31,c_1669]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_62638,plain,
% 19.65/2.99      ( $false ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_1,c_60423]) ).
% 19.65/2.99  
% 19.65/2.99  
% 19.65/2.99  % SZS output end CNFRefutation for theBenchmark.p
% 19.65/2.99  
% 19.65/2.99  ------                               Statistics
% 19.65/2.99  
% 19.65/2.99  ------ General
% 19.65/2.99  
% 19.65/2.99  abstr_ref_over_cycles:                  0
% 19.65/2.99  abstr_ref_under_cycles:                 0
% 19.65/2.99  gc_basic_clause_elim:                   0
% 19.65/2.99  forced_gc_time:                         0
% 19.65/2.99  parsing_time:                           0.009
% 19.65/2.99  unif_index_cands_time:                  0.
% 19.65/2.99  unif_index_add_time:                    0.
% 19.65/2.99  orderings_time:                         0.
% 19.65/2.99  out_proof_time:                         0.011
% 19.65/2.99  total_time:                             2.412
% 19.65/2.99  num_of_symbols:                         38
% 19.65/2.99  num_of_terms:                           112079
% 19.65/2.99  
% 19.65/2.99  ------ Preprocessing
% 19.65/2.99  
% 19.65/2.99  num_of_splits:                          0
% 19.65/2.99  num_of_split_atoms:                     2
% 19.65/2.99  num_of_reused_defs:                     5
% 19.65/2.99  num_eq_ax_congr_red:                    0
% 19.65/2.99  num_of_sem_filtered_clauses:            0
% 19.65/2.99  num_of_subtypes:                        0
% 19.65/2.99  monotx_restored_types:                  0
% 19.65/2.99  sat_num_of_epr_types:                   0
% 19.65/2.99  sat_num_of_non_cyclic_types:            0
% 19.65/2.99  sat_guarded_non_collapsed_types:        0
% 19.65/2.99  num_pure_diseq_elim:                    0
% 19.65/2.99  simp_replaced_by:                       0
% 19.65/2.99  res_preprocessed:                       22
% 19.65/2.99  prep_upred:                             0
% 19.65/2.99  prep_unflattend:                        0
% 19.65/2.99  smt_new_axioms:                         0
% 19.65/2.99  pred_elim_cands:                        0
% 19.65/2.99  pred_elim:                              0
% 19.65/2.99  pred_elim_cl:                           0
% 19.65/2.99  pred_elim_cycles:                       0
% 19.65/2.99  merged_defs:                            0
% 19.65/2.99  merged_defs_ncl:                        0
% 19.65/2.99  bin_hyper_res:                          0
% 19.65/2.99  prep_cycles:                            2
% 19.65/2.99  pred_elim_time:                         0.
% 19.65/2.99  splitting_time:                         0.
% 19.65/2.99  sem_filter_time:                        0.
% 19.65/2.99  monotx_time:                            0.
% 19.65/2.99  subtype_inf_time:                       0.
% 19.65/2.99  
% 19.65/2.99  ------ Problem properties
% 19.65/2.99  
% 19.65/2.99  clauses:                                9
% 19.65/2.99  conjectures:                            1
% 19.65/2.99  epr:                                    0
% 19.65/2.99  horn:                                   9
% 19.65/2.99  ground:                                 1
% 19.65/2.99  unary:                                  9
% 19.65/2.99  binary:                                 0
% 19.65/2.99  lits:                                   9
% 19.65/2.99  lits_eq:                                9
% 19.65/2.99  fd_pure:                                0
% 19.65/2.99  fd_pseudo:                              0
% 19.65/2.99  fd_cond:                                0
% 19.65/2.99  fd_pseudo_cond:                         0
% 19.65/2.99  ac_symbols:                             1
% 19.65/2.99  
% 19.65/2.99  ------ Propositional Solver
% 19.65/2.99  
% 19.65/2.99  prop_solver_calls:                      13
% 19.65/2.99  prop_fast_solver_calls:                 56
% 19.65/2.99  smt_solver_calls:                       0
% 19.65/2.99  smt_fast_solver_calls:                  0
% 19.65/2.99  prop_num_of_clauses:                    364
% 19.65/2.99  prop_preprocess_simplified:             384
% 19.65/2.99  prop_fo_subsumed:                       0
% 19.65/2.99  prop_solver_time:                       0.
% 19.65/2.99  smt_solver_time:                        0.
% 19.65/2.99  smt_fast_solver_time:                   0.
% 19.65/2.99  prop_fast_solver_time:                  0.
% 19.65/2.99  prop_unsat_core_time:                   0.
% 19.65/2.99  
% 19.65/2.99  ------ QBF
% 19.65/2.99  
% 19.65/2.99  qbf_q_res:                              0
% 19.65/2.99  qbf_num_tautologies:                    0
% 19.65/2.99  qbf_prep_cycles:                        0
% 19.65/2.99  
% 19.65/2.99  ------ BMC1
% 19.65/2.99  
% 19.65/2.99  bmc1_current_bound:                     -1
% 19.65/2.99  bmc1_last_solved_bound:                 -1
% 19.65/2.99  bmc1_unsat_core_size:                   -1
% 19.65/2.99  bmc1_unsat_core_parents_size:           -1
% 19.65/2.99  bmc1_merge_next_fun:                    0
% 19.65/2.99  bmc1_unsat_core_clauses_time:           0.
% 19.65/2.99  
% 19.65/2.99  ------ Instantiation
% 19.65/2.99  
% 19.65/2.99  inst_num_of_clauses:                    0
% 19.65/2.99  inst_num_in_passive:                    0
% 19.65/2.99  inst_num_in_active:                     0
% 19.65/2.99  inst_num_in_unprocessed:                0
% 19.65/2.99  inst_num_of_loops:                      0
% 19.65/2.99  inst_num_of_learning_restarts:          0
% 19.65/2.99  inst_num_moves_active_passive:          0
% 19.65/2.99  inst_lit_activity:                      0
% 19.65/2.99  inst_lit_activity_moves:                0
% 19.65/2.99  inst_num_tautologies:                   0
% 19.65/2.99  inst_num_prop_implied:                  0
% 19.65/2.99  inst_num_existing_simplified:           0
% 19.65/2.99  inst_num_eq_res_simplified:             0
% 19.65/2.99  inst_num_child_elim:                    0
% 19.65/2.99  inst_num_of_dismatching_blockings:      0
% 19.65/2.99  inst_num_of_non_proper_insts:           0
% 19.65/2.99  inst_num_of_duplicates:                 0
% 19.65/2.99  inst_inst_num_from_inst_to_res:         0
% 19.65/2.99  inst_dismatching_checking_time:         0.
% 19.65/2.99  
% 19.65/2.99  ------ Resolution
% 19.65/2.99  
% 19.65/2.99  res_num_of_clauses:                     0
% 19.65/2.99  res_num_in_passive:                     0
% 19.65/2.99  res_num_in_active:                      0
% 19.65/2.99  res_num_of_loops:                       24
% 19.65/2.99  res_forward_subset_subsumed:            0
% 19.65/2.99  res_backward_subset_subsumed:           0
% 19.65/2.99  res_forward_subsumed:                   0
% 19.65/2.99  res_backward_subsumed:                  0
% 19.65/2.99  res_forward_subsumption_resolution:     0
% 19.65/2.99  res_backward_subsumption_resolution:    0
% 19.65/2.99  res_clause_to_clause_subsumption:       196446
% 19.65/2.99  res_orphan_elimination:                 0
% 19.65/2.99  res_tautology_del:                      0
% 19.65/2.99  res_num_eq_res_simplified:              0
% 19.65/2.99  res_num_sel_changes:                    0
% 19.65/2.99  res_moves_from_active_to_pass:          0
% 19.65/2.99  
% 19.65/2.99  ------ Superposition
% 19.65/2.99  
% 19.65/2.99  sup_time_total:                         0.
% 19.65/2.99  sup_time_generating:                    0.
% 19.65/2.99  sup_time_sim_full:                      0.
% 19.65/2.99  sup_time_sim_immed:                     0.
% 19.65/2.99  
% 19.65/2.99  sup_num_of_clauses:                     7033
% 19.65/2.99  sup_num_in_active:                      158
% 19.65/2.99  sup_num_in_passive:                     6875
% 19.65/2.99  sup_num_of_loops:                       219
% 19.65/2.99  sup_fw_superposition:                   22931
% 19.65/2.99  sup_bw_superposition:                   18395
% 19.65/2.99  sup_immediate_simplified:               18788
% 19.65/2.99  sup_given_eliminated:                   8
% 19.65/2.99  comparisons_done:                       0
% 19.65/2.99  comparisons_avoided:                    0
% 19.65/2.99  
% 19.65/2.99  ------ Simplifications
% 19.65/2.99  
% 19.65/2.99  
% 19.65/2.99  sim_fw_subset_subsumed:                 0
% 19.65/2.99  sim_bw_subset_subsumed:                 0
% 19.65/2.99  sim_fw_subsumed:                        2884
% 19.65/2.99  sim_bw_subsumed:                        71
% 19.65/2.99  sim_fw_subsumption_res:                 0
% 19.65/2.99  sim_bw_subsumption_res:                 0
% 19.65/2.99  sim_tautology_del:                      0
% 19.65/2.99  sim_eq_tautology_del:                   5140
% 19.65/2.99  sim_eq_res_simp:                        0
% 19.65/2.99  sim_fw_demodulated:                     13537
% 19.65/2.99  sim_bw_demodulated:                     384
% 19.65/2.99  sim_light_normalised:                   7164
% 19.65/2.99  sim_joinable_taut:                      42
% 19.65/2.99  sim_joinable_simp:                      0
% 19.65/2.99  sim_ac_normalised:                      0
% 19.65/2.99  sim_smt_subsumption:                    0
% 19.65/2.99  
%------------------------------------------------------------------------------
