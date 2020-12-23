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
% DateTime   : Thu Dec  3 11:25:05 EST 2020

% Result     : Theorem 11.81s
% Output     : CNFRefutation 11.81s
% Verified   : 
% Statistics : Number of formulae       :  120 (7514 expanded)
%              Number of clauses        :   93 (2794 expanded)
%              Number of leaves         :   11 (2180 expanded)
%              Depth                    :   37
%              Number of atoms          :  121 (7515 expanded)
%              Number of equality atoms :  120 (7514 expanded)
%              Maximal formula depth    :    5 (   1 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f16,f22,f22])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f18,f17,f22])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f9])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f10,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f10])).

fof(f12,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f11])).

fof(f13,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).

fof(f24,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f27,plain,(
    k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(definition_unfolding,[],[f24,f22,f17,f17])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_2,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_5,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_52,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_5])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_6,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_41,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_6])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_43,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_41,c_4])).

cnf(c_57,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_43,c_5])).

cnf(c_68,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_57,c_6])).

cnf(c_105,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_68])).

cnf(c_341,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_52,c_105])).

cnf(c_562,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_341])).

cnf(c_646,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_562])).

cnf(c_1470,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_646])).

cnf(c_61,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_5,c_1])).

cnf(c_1150,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_105,c_61])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_1334,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1150,c_3,c_5])).

cnf(c_1601,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1470,c_1334])).

cnf(c_1771,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2,c_1601])).

cnf(c_7,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_25,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_0,c_7])).

cnf(c_51138,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k1_xboole_0) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_1771,c_25])).

cnf(c_85,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_43,c_2])).

cnf(c_90,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X0),X0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_85,c_4,c_43])).

cnf(c_26,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_91,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X0),X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_90,c_26])).

cnf(c_134,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X0))) = k4_xboole_0(k2_xboole_0(X0,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_91,c_1])).

cnf(c_137,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(demodulation,[status(thm)],[c_134,c_4,c_68])).

cnf(c_58,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_5,c_5])).

cnf(c_67,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_58,c_5])).

cnf(c_4354,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_67,c_68])).

cnf(c_8065,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,k2_xboole_0(X0,X2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_4354])).

cnf(c_8900,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_137,c_8065])).

cnf(c_64,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_43])).

cnf(c_158,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_64])).

cnf(c_24698,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),k2_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8900,c_158])).

cnf(c_24938,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_24698,c_3])).

cnf(c_62,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_5,c_1])).

cnf(c_66,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_62,c_5])).

cnf(c_2389,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_137,c_66])).

cnf(c_2601,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2389,c_64])).

cnf(c_3117,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2601,c_1334])).

cnf(c_3136,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3117,c_4])).

cnf(c_3209,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_3136,c_5])).

cnf(c_3149,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_5,c_3136])).

cnf(c_3353,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_3149])).

cnf(c_5362,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_3209,c_3353])).

cnf(c_8736,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_5362,c_5])).

cnf(c_9925,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X0),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8900,c_8736])).

cnf(c_10544,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X0))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_9925,c_1])).

cnf(c_10597,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(demodulation,[status(thm)],[c_10544,c_4,c_3149])).

cnf(c_10606,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_10597])).

cnf(c_25140,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),k1_xboole_0),X0) = X0 ),
    inference(superposition,[status(thm)],[c_24938,c_10606])).

cnf(c_9901,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)),X2)) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0),X2) ),
    inference(superposition,[status(thm)],[c_8900,c_52])).

cnf(c_9936,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0),X2) = k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(k1_xboole_0,X2)) ),
    inference(demodulation,[status(thm)],[c_9901,c_8900])).

cnf(c_9937,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X2) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(demodulation,[status(thm)],[c_9936,c_4,c_5,c_26])).

cnf(c_14297,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X2,X3)) ),
    inference(superposition,[status(thm)],[c_9937,c_5])).

cnf(c_25317,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k1_xboole_0)),X1) = X1 ),
    inference(demodulation,[status(thm)],[c_25140,c_14297])).

cnf(c_25318,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),X1) = X1 ),
    inference(light_normalisation,[status(thm)],[c_25317,c_3])).

cnf(c_26010,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))),X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_25318,c_52])).

cnf(c_26070,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_26010,c_4,c_68])).

cnf(c_26257,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_26070,c_9937])).

cnf(c_26407,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))),X2) ),
    inference(superposition,[status(thm)],[c_26257,c_52])).

cnf(c_26501,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
    inference(light_normalisation,[status(thm)],[c_26407,c_4,c_68])).

cnf(c_9667,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8736,c_43])).

cnf(c_10093,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_9667,c_1])).

cnf(c_10151,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(demodulation,[status(thm)],[c_10093,c_4,c_3353])).

cnf(c_10245,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_10151])).

cnf(c_10908,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_3149,c_10245])).

cnf(c_11435,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_10908])).

cnf(c_1817,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_1601,c_5])).

cnf(c_1832,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1817,c_5,c_6])).

cnf(c_12032,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11435,c_1832])).

cnf(c_601,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_341,c_5])).

cnf(c_26192,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_26070,c_601])).

cnf(c_30134,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_26192,c_10245])).

cnf(c_14322,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_9937,c_4])).

cnf(c_30204,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(light_normalisation,[status(thm)],[c_30134,c_14322])).

cnf(c_8074,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_4354])).

cnf(c_10373,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10151,c_8074])).

cnf(c_15620,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k1_xboole_0),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_10373,c_10606])).

cnf(c_15736,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
    inference(demodulation,[status(thm)],[c_15620,c_14322])).

cnf(c_30205,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_30204,c_15736])).

cnf(c_30455,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_1,c_30205])).

cnf(c_30862,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_30455,c_10597])).

cnf(c_36899,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X1,X0),X2))),k1_xboole_0) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_12032,c_30862])).

cnf(c_14277,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X1,X0),X2))) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_9937,c_1334])).

cnf(c_37099,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k1_xboole_0) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(light_normalisation,[status(thm)],[c_36899,c_14277])).

cnf(c_51139,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_51138,c_26501,c_37099])).

cnf(c_52371,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1,c_51139])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:25:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 11.81/2.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.81/2.01  
% 11.81/2.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.81/2.01  
% 11.81/2.01  ------  iProver source info
% 11.81/2.01  
% 11.81/2.01  git: date: 2020-06-30 10:37:57 +0100
% 11.81/2.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.81/2.01  git: non_committed_changes: false
% 11.81/2.01  git: last_make_outside_of_git: false
% 11.81/2.01  
% 11.81/2.01  ------ 
% 11.81/2.01  
% 11.81/2.01  ------ Input Options
% 11.81/2.01  
% 11.81/2.01  --out_options                           all
% 11.81/2.01  --tptp_safe_out                         true
% 11.81/2.01  --problem_path                          ""
% 11.81/2.01  --include_path                          ""
% 11.81/2.01  --clausifier                            res/vclausify_rel
% 11.81/2.01  --clausifier_options                    --mode clausify
% 11.81/2.01  --stdin                                 false
% 11.81/2.01  --stats_out                             all
% 11.81/2.01  
% 11.81/2.01  ------ General Options
% 11.81/2.01  
% 11.81/2.01  --fof                                   false
% 11.81/2.01  --time_out_real                         305.
% 11.81/2.01  --time_out_virtual                      -1.
% 11.81/2.01  --symbol_type_check                     false
% 11.81/2.01  --clausify_out                          false
% 11.81/2.01  --sig_cnt_out                           false
% 11.81/2.01  --trig_cnt_out                          false
% 11.81/2.01  --trig_cnt_out_tolerance                1.
% 11.81/2.01  --trig_cnt_out_sk_spl                   false
% 11.81/2.01  --abstr_cl_out                          false
% 11.81/2.01  
% 11.81/2.01  ------ Global Options
% 11.81/2.01  
% 11.81/2.01  --schedule                              default
% 11.81/2.01  --add_important_lit                     false
% 11.81/2.01  --prop_solver_per_cl                    1000
% 11.81/2.01  --min_unsat_core                        false
% 11.81/2.01  --soft_assumptions                      false
% 11.81/2.01  --soft_lemma_size                       3
% 11.81/2.01  --prop_impl_unit_size                   0
% 11.81/2.01  --prop_impl_unit                        []
% 11.81/2.01  --share_sel_clauses                     true
% 11.81/2.01  --reset_solvers                         false
% 11.81/2.01  --bc_imp_inh                            [conj_cone]
% 11.81/2.01  --conj_cone_tolerance                   3.
% 11.81/2.01  --extra_neg_conj                        none
% 11.81/2.01  --large_theory_mode                     true
% 11.81/2.01  --prolific_symb_bound                   200
% 11.81/2.01  --lt_threshold                          2000
% 11.81/2.01  --clause_weak_htbl                      true
% 11.81/2.01  --gc_record_bc_elim                     false
% 11.81/2.01  
% 11.81/2.01  ------ Preprocessing Options
% 11.81/2.01  
% 11.81/2.01  --preprocessing_flag                    true
% 11.81/2.01  --time_out_prep_mult                    0.1
% 11.81/2.01  --splitting_mode                        input
% 11.81/2.01  --splitting_grd                         true
% 11.81/2.01  --splitting_cvd                         false
% 11.81/2.01  --splitting_cvd_svl                     false
% 11.81/2.01  --splitting_nvd                         32
% 11.81/2.01  --sub_typing                            true
% 11.81/2.01  --prep_gs_sim                           true
% 11.81/2.01  --prep_unflatten                        true
% 11.81/2.01  --prep_res_sim                          true
% 11.81/2.01  --prep_upred                            true
% 11.81/2.01  --prep_sem_filter                       exhaustive
% 11.81/2.01  --prep_sem_filter_out                   false
% 11.81/2.01  --pred_elim                             true
% 11.81/2.01  --res_sim_input                         true
% 11.81/2.01  --eq_ax_congr_red                       true
% 11.81/2.01  --pure_diseq_elim                       true
% 11.81/2.01  --brand_transform                       false
% 11.81/2.01  --non_eq_to_eq                          false
% 11.81/2.01  --prep_def_merge                        true
% 11.81/2.01  --prep_def_merge_prop_impl              false
% 11.81/2.01  --prep_def_merge_mbd                    true
% 11.81/2.01  --prep_def_merge_tr_red                 false
% 11.81/2.01  --prep_def_merge_tr_cl                  false
% 11.81/2.01  --smt_preprocessing                     true
% 11.81/2.01  --smt_ac_axioms                         fast
% 11.81/2.01  --preprocessed_out                      false
% 11.81/2.01  --preprocessed_stats                    false
% 11.81/2.01  
% 11.81/2.01  ------ Abstraction refinement Options
% 11.81/2.01  
% 11.81/2.01  --abstr_ref                             []
% 11.81/2.01  --abstr_ref_prep                        false
% 11.81/2.01  --abstr_ref_until_sat                   false
% 11.81/2.01  --abstr_ref_sig_restrict                funpre
% 11.81/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 11.81/2.01  --abstr_ref_under                       []
% 11.81/2.01  
% 11.81/2.01  ------ SAT Options
% 11.81/2.01  
% 11.81/2.01  --sat_mode                              false
% 11.81/2.01  --sat_fm_restart_options                ""
% 11.81/2.01  --sat_gr_def                            false
% 11.81/2.01  --sat_epr_types                         true
% 11.81/2.01  --sat_non_cyclic_types                  false
% 11.81/2.01  --sat_finite_models                     false
% 11.81/2.01  --sat_fm_lemmas                         false
% 11.81/2.01  --sat_fm_prep                           false
% 11.81/2.01  --sat_fm_uc_incr                        true
% 11.81/2.01  --sat_out_model                         small
% 11.81/2.01  --sat_out_clauses                       false
% 11.81/2.01  
% 11.81/2.01  ------ QBF Options
% 11.81/2.01  
% 11.81/2.01  --qbf_mode                              false
% 11.81/2.01  --qbf_elim_univ                         false
% 11.81/2.01  --qbf_dom_inst                          none
% 11.81/2.01  --qbf_dom_pre_inst                      false
% 11.81/2.01  --qbf_sk_in                             false
% 11.81/2.01  --qbf_pred_elim                         true
% 11.81/2.01  --qbf_split                             512
% 11.81/2.01  
% 11.81/2.01  ------ BMC1 Options
% 11.81/2.01  
% 11.81/2.01  --bmc1_incremental                      false
% 11.81/2.01  --bmc1_axioms                           reachable_all
% 11.81/2.01  --bmc1_min_bound                        0
% 11.81/2.01  --bmc1_max_bound                        -1
% 11.81/2.01  --bmc1_max_bound_default                -1
% 11.81/2.01  --bmc1_symbol_reachability              true
% 11.81/2.01  --bmc1_property_lemmas                  false
% 11.81/2.01  --bmc1_k_induction                      false
% 11.81/2.01  --bmc1_non_equiv_states                 false
% 11.81/2.01  --bmc1_deadlock                         false
% 11.81/2.01  --bmc1_ucm                              false
% 11.81/2.01  --bmc1_add_unsat_core                   none
% 11.81/2.01  --bmc1_unsat_core_children              false
% 11.81/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 11.81/2.01  --bmc1_out_stat                         full
% 11.81/2.01  --bmc1_ground_init                      false
% 11.81/2.01  --bmc1_pre_inst_next_state              false
% 11.81/2.01  --bmc1_pre_inst_state                   false
% 11.81/2.01  --bmc1_pre_inst_reach_state             false
% 11.81/2.01  --bmc1_out_unsat_core                   false
% 11.81/2.01  --bmc1_aig_witness_out                  false
% 11.81/2.01  --bmc1_verbose                          false
% 11.81/2.01  --bmc1_dump_clauses_tptp                false
% 11.81/2.01  --bmc1_dump_unsat_core_tptp             false
% 11.81/2.01  --bmc1_dump_file                        -
% 11.81/2.01  --bmc1_ucm_expand_uc_limit              128
% 11.81/2.01  --bmc1_ucm_n_expand_iterations          6
% 11.81/2.01  --bmc1_ucm_extend_mode                  1
% 11.81/2.01  --bmc1_ucm_init_mode                    2
% 11.81/2.01  --bmc1_ucm_cone_mode                    none
% 11.81/2.01  --bmc1_ucm_reduced_relation_type        0
% 11.81/2.01  --bmc1_ucm_relax_model                  4
% 11.81/2.01  --bmc1_ucm_full_tr_after_sat            true
% 11.81/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 11.81/2.01  --bmc1_ucm_layered_model                none
% 11.81/2.01  --bmc1_ucm_max_lemma_size               10
% 11.81/2.01  
% 11.81/2.01  ------ AIG Options
% 11.81/2.01  
% 11.81/2.01  --aig_mode                              false
% 11.81/2.01  
% 11.81/2.01  ------ Instantiation Options
% 11.81/2.01  
% 11.81/2.01  --instantiation_flag                    true
% 11.81/2.01  --inst_sos_flag                         false
% 11.81/2.01  --inst_sos_phase                        true
% 11.81/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.81/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.81/2.01  --inst_lit_sel_side                     num_symb
% 11.81/2.01  --inst_solver_per_active                1400
% 11.81/2.01  --inst_solver_calls_frac                1.
% 11.81/2.01  --inst_passive_queue_type               priority_queues
% 11.81/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.81/2.01  --inst_passive_queues_freq              [25;2]
% 11.81/2.01  --inst_dismatching                      true
% 11.81/2.01  --inst_eager_unprocessed_to_passive     true
% 11.81/2.01  --inst_prop_sim_given                   true
% 11.81/2.01  --inst_prop_sim_new                     false
% 11.81/2.01  --inst_subs_new                         false
% 11.81/2.01  --inst_eq_res_simp                      false
% 11.81/2.01  --inst_subs_given                       false
% 11.81/2.01  --inst_orphan_elimination               true
% 11.81/2.01  --inst_learning_loop_flag               true
% 11.81/2.01  --inst_learning_start                   3000
% 11.81/2.01  --inst_learning_factor                  2
% 11.81/2.01  --inst_start_prop_sim_after_learn       3
% 11.81/2.01  --inst_sel_renew                        solver
% 11.81/2.01  --inst_lit_activity_flag                true
% 11.81/2.01  --inst_restr_to_given                   false
% 11.81/2.01  --inst_activity_threshold               500
% 11.81/2.01  --inst_out_proof                        true
% 11.81/2.01  
% 11.81/2.01  ------ Resolution Options
% 11.81/2.01  
% 11.81/2.01  --resolution_flag                       true
% 11.81/2.01  --res_lit_sel                           adaptive
% 11.81/2.01  --res_lit_sel_side                      none
% 11.81/2.01  --res_ordering                          kbo
% 11.81/2.01  --res_to_prop_solver                    active
% 11.81/2.01  --res_prop_simpl_new                    false
% 11.81/2.01  --res_prop_simpl_given                  true
% 11.81/2.01  --res_passive_queue_type                priority_queues
% 11.81/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.81/2.01  --res_passive_queues_freq               [15;5]
% 11.81/2.01  --res_forward_subs                      full
% 11.81/2.01  --res_backward_subs                     full
% 11.81/2.01  --res_forward_subs_resolution           true
% 11.81/2.01  --res_backward_subs_resolution          true
% 11.81/2.01  --res_orphan_elimination                true
% 11.81/2.01  --res_time_limit                        2.
% 11.81/2.01  --res_out_proof                         true
% 11.81/2.01  
% 11.81/2.01  ------ Superposition Options
% 11.81/2.01  
% 11.81/2.01  --superposition_flag                    true
% 11.81/2.01  --sup_passive_queue_type                priority_queues
% 11.81/2.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.81/2.01  --sup_passive_queues_freq               [8;1;4]
% 11.81/2.01  --demod_completeness_check              fast
% 11.81/2.01  --demod_use_ground                      true
% 11.81/2.01  --sup_to_prop_solver                    passive
% 11.81/2.01  --sup_prop_simpl_new                    true
% 11.81/2.01  --sup_prop_simpl_given                  true
% 11.81/2.01  --sup_fun_splitting                     false
% 11.81/2.01  --sup_smt_interval                      50000
% 11.81/2.01  
% 11.81/2.01  ------ Superposition Simplification Setup
% 11.81/2.01  
% 11.81/2.01  --sup_indices_passive                   []
% 11.81/2.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.81/2.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.81/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.81/2.01  --sup_full_triv                         [TrivRules;PropSubs]
% 11.81/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.81/2.01  --sup_full_bw                           [BwDemod]
% 11.81/2.01  --sup_immed_triv                        [TrivRules]
% 11.81/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.81/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.81/2.01  --sup_immed_bw_main                     []
% 11.81/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.81/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 11.81/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.81/2.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.81/2.01  
% 11.81/2.01  ------ Combination Options
% 11.81/2.01  
% 11.81/2.01  --comb_res_mult                         3
% 11.81/2.01  --comb_sup_mult                         2
% 11.81/2.01  --comb_inst_mult                        10
% 11.81/2.01  
% 11.81/2.01  ------ Debug Options
% 11.81/2.01  
% 11.81/2.01  --dbg_backtrace                         false
% 11.81/2.01  --dbg_dump_prop_clauses                 false
% 11.81/2.01  --dbg_dump_prop_clauses_file            -
% 11.81/2.01  --dbg_out_stat                          false
% 11.81/2.01  ------ Parsing...
% 11.81/2.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.81/2.01  
% 11.81/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 11.81/2.01  
% 11.81/2.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.81/2.01  
% 11.81/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.81/2.01  ------ Proving...
% 11.81/2.01  ------ Problem Properties 
% 11.81/2.01  
% 11.81/2.01  
% 11.81/2.01  clauses                                 8
% 11.81/2.01  conjectures                             1
% 11.81/2.01  EPR                                     0
% 11.81/2.01  Horn                                    8
% 11.81/2.01  unary                                   8
% 11.81/2.01  binary                                  0
% 11.81/2.01  lits                                    8
% 11.81/2.01  lits eq                                 8
% 11.81/2.01  fd_pure                                 0
% 11.81/2.01  fd_pseudo                               0
% 11.81/2.01  fd_cond                                 0
% 11.81/2.01  fd_pseudo_cond                          0
% 11.81/2.01  AC symbols                              0
% 11.81/2.01  
% 11.81/2.01  ------ Schedule UEQ
% 11.81/2.01  
% 11.81/2.01  ------ pure equality problem: resolution off 
% 11.81/2.01  
% 11.81/2.01  ------ Option_UEQ Time Limit: Unbounded
% 11.81/2.01  
% 11.81/2.01  
% 11.81/2.01  ------ 
% 11.81/2.01  Current options:
% 11.81/2.01  ------ 
% 11.81/2.01  
% 11.81/2.01  ------ Input Options
% 11.81/2.01  
% 11.81/2.01  --out_options                           all
% 11.81/2.01  --tptp_safe_out                         true
% 11.81/2.01  --problem_path                          ""
% 11.81/2.01  --include_path                          ""
% 11.81/2.01  --clausifier                            res/vclausify_rel
% 11.81/2.01  --clausifier_options                    --mode clausify
% 11.81/2.01  --stdin                                 false
% 11.81/2.01  --stats_out                             all
% 11.81/2.01  
% 11.81/2.01  ------ General Options
% 11.81/2.01  
% 11.81/2.01  --fof                                   false
% 11.81/2.01  --time_out_real                         305.
% 11.81/2.01  --time_out_virtual                      -1.
% 11.81/2.01  --symbol_type_check                     false
% 11.81/2.01  --clausify_out                          false
% 11.81/2.01  --sig_cnt_out                           false
% 11.81/2.01  --trig_cnt_out                          false
% 11.81/2.01  --trig_cnt_out_tolerance                1.
% 11.81/2.01  --trig_cnt_out_sk_spl                   false
% 11.81/2.01  --abstr_cl_out                          false
% 11.81/2.01  
% 11.81/2.01  ------ Global Options
% 11.81/2.01  
% 11.81/2.01  --schedule                              default
% 11.81/2.01  --add_important_lit                     false
% 11.81/2.01  --prop_solver_per_cl                    1000
% 11.81/2.01  --min_unsat_core                        false
% 11.81/2.01  --soft_assumptions                      false
% 11.81/2.01  --soft_lemma_size                       3
% 11.81/2.01  --prop_impl_unit_size                   0
% 11.81/2.01  --prop_impl_unit                        []
% 11.81/2.01  --share_sel_clauses                     true
% 11.81/2.01  --reset_solvers                         false
% 11.81/2.01  --bc_imp_inh                            [conj_cone]
% 11.81/2.01  --conj_cone_tolerance                   3.
% 11.81/2.01  --extra_neg_conj                        none
% 11.81/2.01  --large_theory_mode                     true
% 11.81/2.01  --prolific_symb_bound                   200
% 11.81/2.01  --lt_threshold                          2000
% 11.81/2.01  --clause_weak_htbl                      true
% 11.81/2.01  --gc_record_bc_elim                     false
% 11.81/2.01  
% 11.81/2.01  ------ Preprocessing Options
% 11.81/2.01  
% 11.81/2.01  --preprocessing_flag                    true
% 11.81/2.01  --time_out_prep_mult                    0.1
% 11.81/2.01  --splitting_mode                        input
% 11.81/2.01  --splitting_grd                         true
% 11.81/2.01  --splitting_cvd                         false
% 11.81/2.01  --splitting_cvd_svl                     false
% 11.81/2.01  --splitting_nvd                         32
% 11.81/2.01  --sub_typing                            true
% 11.81/2.01  --prep_gs_sim                           true
% 11.81/2.01  --prep_unflatten                        true
% 11.81/2.01  --prep_res_sim                          true
% 11.81/2.01  --prep_upred                            true
% 11.81/2.01  --prep_sem_filter                       exhaustive
% 11.81/2.01  --prep_sem_filter_out                   false
% 11.81/2.01  --pred_elim                             true
% 11.81/2.01  --res_sim_input                         true
% 11.81/2.01  --eq_ax_congr_red                       true
% 11.81/2.01  --pure_diseq_elim                       true
% 11.81/2.01  --brand_transform                       false
% 11.81/2.01  --non_eq_to_eq                          false
% 11.81/2.01  --prep_def_merge                        true
% 11.81/2.01  --prep_def_merge_prop_impl              false
% 11.81/2.01  --prep_def_merge_mbd                    true
% 11.81/2.01  --prep_def_merge_tr_red                 false
% 11.81/2.01  --prep_def_merge_tr_cl                  false
% 11.81/2.01  --smt_preprocessing                     true
% 11.81/2.01  --smt_ac_axioms                         fast
% 11.81/2.01  --preprocessed_out                      false
% 11.81/2.01  --preprocessed_stats                    false
% 11.81/2.01  
% 11.81/2.01  ------ Abstraction refinement Options
% 11.81/2.01  
% 11.81/2.01  --abstr_ref                             []
% 11.81/2.01  --abstr_ref_prep                        false
% 11.81/2.01  --abstr_ref_until_sat                   false
% 11.81/2.01  --abstr_ref_sig_restrict                funpre
% 11.81/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 11.81/2.01  --abstr_ref_under                       []
% 11.81/2.01  
% 11.81/2.01  ------ SAT Options
% 11.81/2.01  
% 11.81/2.01  --sat_mode                              false
% 11.81/2.01  --sat_fm_restart_options                ""
% 11.81/2.01  --sat_gr_def                            false
% 11.81/2.01  --sat_epr_types                         true
% 11.81/2.01  --sat_non_cyclic_types                  false
% 11.81/2.01  --sat_finite_models                     false
% 11.81/2.01  --sat_fm_lemmas                         false
% 11.81/2.01  --sat_fm_prep                           false
% 11.81/2.01  --sat_fm_uc_incr                        true
% 11.81/2.01  --sat_out_model                         small
% 11.81/2.01  --sat_out_clauses                       false
% 11.81/2.01  
% 11.81/2.01  ------ QBF Options
% 11.81/2.01  
% 11.81/2.01  --qbf_mode                              false
% 11.81/2.01  --qbf_elim_univ                         false
% 11.81/2.01  --qbf_dom_inst                          none
% 11.81/2.01  --qbf_dom_pre_inst                      false
% 11.81/2.01  --qbf_sk_in                             false
% 11.81/2.01  --qbf_pred_elim                         true
% 11.81/2.01  --qbf_split                             512
% 11.81/2.01  
% 11.81/2.01  ------ BMC1 Options
% 11.81/2.01  
% 11.81/2.01  --bmc1_incremental                      false
% 11.81/2.01  --bmc1_axioms                           reachable_all
% 11.81/2.01  --bmc1_min_bound                        0
% 11.81/2.01  --bmc1_max_bound                        -1
% 11.81/2.01  --bmc1_max_bound_default                -1
% 11.81/2.01  --bmc1_symbol_reachability              true
% 11.81/2.01  --bmc1_property_lemmas                  false
% 11.81/2.01  --bmc1_k_induction                      false
% 11.81/2.01  --bmc1_non_equiv_states                 false
% 11.81/2.01  --bmc1_deadlock                         false
% 11.81/2.01  --bmc1_ucm                              false
% 11.81/2.01  --bmc1_add_unsat_core                   none
% 11.81/2.01  --bmc1_unsat_core_children              false
% 11.81/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 11.81/2.01  --bmc1_out_stat                         full
% 11.81/2.01  --bmc1_ground_init                      false
% 11.81/2.01  --bmc1_pre_inst_next_state              false
% 11.81/2.01  --bmc1_pre_inst_state                   false
% 11.81/2.01  --bmc1_pre_inst_reach_state             false
% 11.81/2.01  --bmc1_out_unsat_core                   false
% 11.81/2.01  --bmc1_aig_witness_out                  false
% 11.81/2.01  --bmc1_verbose                          false
% 11.81/2.01  --bmc1_dump_clauses_tptp                false
% 11.81/2.01  --bmc1_dump_unsat_core_tptp             false
% 11.81/2.01  --bmc1_dump_file                        -
% 11.81/2.01  --bmc1_ucm_expand_uc_limit              128
% 11.81/2.01  --bmc1_ucm_n_expand_iterations          6
% 11.81/2.01  --bmc1_ucm_extend_mode                  1
% 11.81/2.01  --bmc1_ucm_init_mode                    2
% 11.81/2.01  --bmc1_ucm_cone_mode                    none
% 11.81/2.01  --bmc1_ucm_reduced_relation_type        0
% 11.81/2.01  --bmc1_ucm_relax_model                  4
% 11.81/2.01  --bmc1_ucm_full_tr_after_sat            true
% 11.81/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 11.81/2.01  --bmc1_ucm_layered_model                none
% 11.81/2.01  --bmc1_ucm_max_lemma_size               10
% 11.81/2.01  
% 11.81/2.01  ------ AIG Options
% 11.81/2.01  
% 11.81/2.01  --aig_mode                              false
% 11.81/2.01  
% 11.81/2.01  ------ Instantiation Options
% 11.81/2.01  
% 11.81/2.01  --instantiation_flag                    false
% 11.81/2.01  --inst_sos_flag                         false
% 11.81/2.01  --inst_sos_phase                        true
% 11.81/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.81/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.81/2.01  --inst_lit_sel_side                     num_symb
% 11.81/2.01  --inst_solver_per_active                1400
% 11.81/2.01  --inst_solver_calls_frac                1.
% 11.81/2.01  --inst_passive_queue_type               priority_queues
% 11.81/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.81/2.01  --inst_passive_queues_freq              [25;2]
% 11.81/2.01  --inst_dismatching                      true
% 11.81/2.01  --inst_eager_unprocessed_to_passive     true
% 11.81/2.01  --inst_prop_sim_given                   true
% 11.81/2.01  --inst_prop_sim_new                     false
% 11.81/2.01  --inst_subs_new                         false
% 11.81/2.01  --inst_eq_res_simp                      false
% 11.81/2.01  --inst_subs_given                       false
% 11.81/2.01  --inst_orphan_elimination               true
% 11.81/2.01  --inst_learning_loop_flag               true
% 11.81/2.01  --inst_learning_start                   3000
% 11.81/2.01  --inst_learning_factor                  2
% 11.81/2.01  --inst_start_prop_sim_after_learn       3
% 11.81/2.01  --inst_sel_renew                        solver
% 11.81/2.01  --inst_lit_activity_flag                true
% 11.81/2.01  --inst_restr_to_given                   false
% 11.81/2.01  --inst_activity_threshold               500
% 11.81/2.01  --inst_out_proof                        true
% 11.81/2.01  
% 11.81/2.01  ------ Resolution Options
% 11.81/2.01  
% 11.81/2.01  --resolution_flag                       false
% 11.81/2.01  --res_lit_sel                           adaptive
% 11.81/2.01  --res_lit_sel_side                      none
% 11.81/2.01  --res_ordering                          kbo
% 11.81/2.01  --res_to_prop_solver                    active
% 11.81/2.01  --res_prop_simpl_new                    false
% 11.81/2.01  --res_prop_simpl_given                  true
% 11.81/2.01  --res_passive_queue_type                priority_queues
% 11.81/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.81/2.01  --res_passive_queues_freq               [15;5]
% 11.81/2.01  --res_forward_subs                      full
% 11.81/2.01  --res_backward_subs                     full
% 11.81/2.01  --res_forward_subs_resolution           true
% 11.81/2.01  --res_backward_subs_resolution          true
% 11.81/2.01  --res_orphan_elimination                true
% 11.81/2.01  --res_time_limit                        2.
% 11.81/2.01  --res_out_proof                         true
% 11.81/2.01  
% 11.81/2.01  ------ Superposition Options
% 11.81/2.01  
% 11.81/2.01  --superposition_flag                    true
% 11.81/2.01  --sup_passive_queue_type                priority_queues
% 11.81/2.01  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.81/2.01  --sup_passive_queues_freq               [8;1;4]
% 11.81/2.01  --demod_completeness_check              fast
% 11.81/2.01  --demod_use_ground                      true
% 11.81/2.01  --sup_to_prop_solver                    active
% 11.81/2.01  --sup_prop_simpl_new                    false
% 11.81/2.01  --sup_prop_simpl_given                  false
% 11.81/2.01  --sup_fun_splitting                     true
% 11.81/2.01  --sup_smt_interval                      10000
% 11.81/2.01  
% 11.81/2.01  ------ Superposition Simplification Setup
% 11.81/2.01  
% 11.81/2.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.81/2.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.81/2.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.81/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.81/2.01  --sup_full_triv                         [TrivRules]
% 11.81/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.81/2.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.81/2.01  --sup_immed_triv                        [TrivRules]
% 11.81/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.81/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.81/2.01  --sup_immed_bw_main                     []
% 11.81/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.81/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 11.81/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.81/2.01  --sup_input_bw                          [BwDemod;BwSubsumption]
% 11.81/2.01  
% 11.81/2.01  ------ Combination Options
% 11.81/2.01  
% 11.81/2.01  --comb_res_mult                         1
% 11.81/2.01  --comb_sup_mult                         1
% 11.81/2.01  --comb_inst_mult                        1000000
% 11.81/2.01  
% 11.81/2.01  ------ Debug Options
% 11.81/2.01  
% 11.81/2.01  --dbg_backtrace                         false
% 11.81/2.01  --dbg_dump_prop_clauses                 false
% 11.81/2.01  --dbg_dump_prop_clauses_file            -
% 11.81/2.01  --dbg_out_stat                          false
% 11.81/2.01  
% 11.81/2.01  
% 11.81/2.01  
% 11.81/2.01  
% 11.81/2.01  ------ Proving...
% 11.81/2.01  
% 11.81/2.01  
% 11.81/2.01  % SZS status Theorem for theBenchmark.p
% 11.81/2.01  
% 11.81/2.01   Resolution empty clause
% 11.81/2.01  
% 11.81/2.01  % SZS output start CNFRefutation for theBenchmark.p
% 11.81/2.01  
% 11.81/2.01  fof(f2,axiom,(
% 11.81/2.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.81/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/2.01  
% 11.81/2.01  fof(f16,plain,(
% 11.81/2.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.81/2.01    inference(cnf_transformation,[],[f2])).
% 11.81/2.01  
% 11.81/2.01  fof(f8,axiom,(
% 11.81/2.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.81/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/2.01  
% 11.81/2.01  fof(f22,plain,(
% 11.81/2.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.81/2.01    inference(cnf_transformation,[],[f8])).
% 11.81/2.01  
% 11.81/2.01  fof(f25,plain,(
% 11.81/2.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 11.81/2.01    inference(definition_unfolding,[],[f16,f22,f22])).
% 11.81/2.01  
% 11.81/2.01  fof(f4,axiom,(
% 11.81/2.01    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 11.81/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/2.01  
% 11.81/2.01  fof(f18,plain,(
% 11.81/2.01    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 11.81/2.01    inference(cnf_transformation,[],[f4])).
% 11.81/2.01  
% 11.81/2.01  fof(f3,axiom,(
% 11.81/2.01    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 11.81/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/2.01  
% 11.81/2.01  fof(f17,plain,(
% 11.81/2.01    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 11.81/2.01    inference(cnf_transformation,[],[f3])).
% 11.81/2.01  
% 11.81/2.01  fof(f26,plain,(
% 11.81/2.01    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 11.81/2.01    inference(definition_unfolding,[],[f18,f17,f22])).
% 11.81/2.01  
% 11.81/2.01  fof(f7,axiom,(
% 11.81/2.01    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 11.81/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/2.01  
% 11.81/2.01  fof(f21,plain,(
% 11.81/2.01    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 11.81/2.01    inference(cnf_transformation,[],[f7])).
% 11.81/2.01  
% 11.81/2.01  fof(f1,axiom,(
% 11.81/2.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 11.81/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/2.01  
% 11.81/2.01  fof(f15,plain,(
% 11.81/2.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 11.81/2.01    inference(cnf_transformation,[],[f1])).
% 11.81/2.01  
% 11.81/2.01  fof(f9,axiom,(
% 11.81/2.01    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 11.81/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/2.01  
% 11.81/2.01  fof(f23,plain,(
% 11.81/2.01    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 11.81/2.01    inference(cnf_transformation,[],[f9])).
% 11.81/2.01  
% 11.81/2.01  fof(f6,axiom,(
% 11.81/2.01    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 11.81/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/2.01  
% 11.81/2.01  fof(f20,plain,(
% 11.81/2.01    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.81/2.01    inference(cnf_transformation,[],[f6])).
% 11.81/2.01  
% 11.81/2.01  fof(f5,axiom,(
% 11.81/2.01    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 11.81/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/2.01  
% 11.81/2.01  fof(f19,plain,(
% 11.81/2.01    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.81/2.01    inference(cnf_transformation,[],[f5])).
% 11.81/2.01  
% 11.81/2.01  fof(f10,conjecture,(
% 11.81/2.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 11.81/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/2.01  
% 11.81/2.01  fof(f11,negated_conjecture,(
% 11.81/2.01    ~! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 11.81/2.01    inference(negated_conjecture,[],[f10])).
% 11.81/2.01  
% 11.81/2.01  fof(f12,plain,(
% 11.81/2.01    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 11.81/2.01    inference(ennf_transformation,[],[f11])).
% 11.81/2.01  
% 11.81/2.01  fof(f13,plain,(
% 11.81/2.01    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 11.81/2.01    introduced(choice_axiom,[])).
% 11.81/2.01  
% 11.81/2.01  fof(f14,plain,(
% 11.81/2.01    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 11.81/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).
% 11.81/2.01  
% 11.81/2.01  fof(f24,plain,(
% 11.81/2.01    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 11.81/2.01    inference(cnf_transformation,[],[f14])).
% 11.81/2.01  
% 11.81/2.01  fof(f27,plain,(
% 11.81/2.01    k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 11.81/2.01    inference(definition_unfolding,[],[f24,f22,f17,f17])).
% 11.81/2.01  
% 11.81/2.01  cnf(c_1,plain,
% 11.81/2.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.81/2.01      inference(cnf_transformation,[],[f25]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_2,plain,
% 11.81/2.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
% 11.81/2.01      inference(cnf_transformation,[],[f26]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_5,plain,
% 11.81/2.01      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.81/2.01      inference(cnf_transformation,[],[f21]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_52,plain,
% 11.81/2.01      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_1,c_5]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_0,plain,
% 11.81/2.01      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 11.81/2.01      inference(cnf_transformation,[],[f15]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_6,plain,
% 11.81/2.01      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.81/2.01      inference(cnf_transformation,[],[f23]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_41,plain,
% 11.81/2.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_1,c_6]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_4,plain,
% 11.81/2.01      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.81/2.01      inference(cnf_transformation,[],[f20]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_43,plain,
% 11.81/2.01      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.81/2.01      inference(light_normalisation,[status(thm)],[c_41,c_4]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_57,plain,
% 11.81/2.01      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_43,c_5]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_68,plain,
% 11.81/2.01      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.81/2.01      inference(demodulation,[status(thm)],[c_57,c_6]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_105,plain,
% 11.81/2.01      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_0,c_68]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_341,plain,
% 11.81/2.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_52,c_105]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_562,plain,
% 11.81/2.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k1_xboole_0 ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_1,c_341]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_646,plain,
% 11.81/2.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),X0) = k1_xboole_0 ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_1,c_562]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_1470,plain,
% 11.81/2.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X0) = k1_xboole_0 ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_1,c_646]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_61,plain,
% 11.81/2.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_5,c_1]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_1150,plain,
% 11.81/2.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_105,c_61]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_3,plain,
% 11.81/2.01      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.81/2.01      inference(cnf_transformation,[],[f19]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_1334,plain,
% 11.81/2.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 11.81/2.01      inference(demodulation,[status(thm)],[c_1150,c_3,c_5]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_1601,plain,
% 11.81/2.01      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 11.81/2.01      inference(light_normalisation,[status(thm)],[c_1470,c_1334]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_1771,plain,
% 11.81/2.01      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_2,c_1601]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_7,negated_conjecture,
% 11.81/2.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 11.81/2.01      inference(cnf_transformation,[],[f27]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_25,plain,
% 11.81/2.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 11.81/2.01      inference(demodulation,[status(thm)],[c_0,c_7]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_51138,plain,
% 11.81/2.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k1_xboole_0) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 11.81/2.01      inference(demodulation,[status(thm)],[c_1771,c_25]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_85,plain,
% 11.81/2.01      ( k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(X0,k1_xboole_0)) ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_43,c_2]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_90,plain,
% 11.81/2.01      ( k4_xboole_0(k2_xboole_0(X0,X0),X0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 11.81/2.01      inference(light_normalisation,[status(thm)],[c_85,c_4,c_43]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_26,plain,
% 11.81/2.01      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_91,plain,
% 11.81/2.01      ( k4_xboole_0(k2_xboole_0(X0,X0),X0) = k1_xboole_0 ),
% 11.81/2.01      inference(demodulation,[status(thm)],[c_90,c_26]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_134,plain,
% 11.81/2.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X0))) = k4_xboole_0(k2_xboole_0(X0,X0),k1_xboole_0) ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_91,c_1]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_137,plain,
% 11.81/2.01      ( k2_xboole_0(X0,X0) = X0 ),
% 11.81/2.01      inference(demodulation,[status(thm)],[c_134,c_4,c_68]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_58,plain,
% 11.81/2.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_5,c_5]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_67,plain,
% 11.81/2.01      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 11.81/2.01      inference(demodulation,[status(thm)],[c_58,c_5]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_4354,plain,
% 11.81/2.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_67,c_68]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_8065,plain,
% 11.81/2.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,k2_xboole_0(X0,X2))) = k1_xboole_0 ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_0,c_4354]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_8900,plain,
% 11.81/2.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_137,c_8065]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_64,plain,
% 11.81/2.01      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_5,c_43]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_158,plain,
% 11.81/2.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k1_xboole_0 ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_5,c_64]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_24698,plain,
% 11.81/2.01      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),k2_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_8900,c_158]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_24938,plain,
% 11.81/2.01      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X0) = k1_xboole_0 ),
% 11.81/2.01      inference(light_normalisation,[status(thm)],[c_24698,c_3]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_62,plain,
% 11.81/2.01      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_5,c_1]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_66,plain,
% 11.81/2.01      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 11.81/2.01      inference(demodulation,[status(thm)],[c_62,c_5]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_2389,plain,
% 11.81/2.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X0))) ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_137,c_66]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_2601,plain,
% 11.81/2.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 11.81/2.01      inference(demodulation,[status(thm)],[c_2389,c_64]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_3117,plain,
% 11.81/2.01      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_2601,c_1334]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_3136,plain,
% 11.81/2.01      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 11.81/2.01      inference(light_normalisation,[status(thm)],[c_3117,c_4]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_3209,plain,
% 11.81/2.01      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_3136,c_5]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_3149,plain,
% 11.81/2.01      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_5,c_3136]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_3353,plain,
% 11.81/2.01      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = X0 ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_0,c_3149]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_5362,plain,
% 11.81/2.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = k4_xboole_0(X0,X1) ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_3209,c_3353]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_8736,plain,
% 11.81/2.01      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,X1) ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_5362,c_5]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_9925,plain,
% 11.81/2.01      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X0),X0) = k1_xboole_0 ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_8900,c_8736]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_10544,plain,
% 11.81/2.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X0))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X0),k1_xboole_0) ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_9925,c_1]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_10597,plain,
% 11.81/2.01      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 11.81/2.01      inference(demodulation,[status(thm)],[c_10544,c_4,c_3149]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_10606,plain,
% 11.81/2.01      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_1,c_10597]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_25140,plain,
% 11.81/2.01      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),k1_xboole_0),X0) = X0 ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_24938,c_10606]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_9901,plain,
% 11.81/2.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)),X2)) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0),X2) ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_8900,c_52]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_9936,plain,
% 11.81/2.01      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0),X2) = k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(k1_xboole_0,X2)) ),
% 11.81/2.01      inference(demodulation,[status(thm)],[c_9901,c_8900]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_9937,plain,
% 11.81/2.01      ( k4_xboole_0(k2_xboole_0(X0,X1),X2) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 11.81/2.01      inference(demodulation,[status(thm)],[c_9936,c_4,c_5,c_26]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_14297,plain,
% 11.81/2.01      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X2,X3)) ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_9937,c_5]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_25317,plain,
% 11.81/2.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k1_xboole_0)),X1) = X1 ),
% 11.81/2.01      inference(demodulation,[status(thm)],[c_25140,c_14297]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_25318,plain,
% 11.81/2.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),X1) = X1 ),
% 11.81/2.01      inference(light_normalisation,[status(thm)],[c_25317,c_3]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_26010,plain,
% 11.81/2.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))),X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_25318,c_52]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_26070,plain,
% 11.81/2.01      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 11.81/2.01      inference(light_normalisation,[status(thm)],[c_26010,c_4,c_68]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_26257,plain,
% 11.81/2.01      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_26070,c_9937]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_26407,plain,
% 11.81/2.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))),X2) ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_26257,c_52]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_26501,plain,
% 11.81/2.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
% 11.81/2.01      inference(light_normalisation,[status(thm)],[c_26407,c_4,c_68]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_9667,plain,
% 11.81/2.01      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k1_xboole_0 ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_8736,c_43]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_10093,plain,
% 11.81/2.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_9667,c_1]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_10151,plain,
% 11.81/2.01      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 11.81/2.01      inference(demodulation,[status(thm)],[c_10093,c_4,c_3353]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_10245,plain,
% 11.81/2.01      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_1,c_10151]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_10908,plain,
% 11.81/2.01      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_3149,c_10245]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_11435,plain,
% 11.81/2.01      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_0,c_10908]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_1817,plain,
% 11.81/2.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_1601,c_5]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_1832,plain,
% 11.81/2.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
% 11.81/2.01      inference(demodulation,[status(thm)],[c_1817,c_5,c_6]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_12032,plain,
% 11.81/2.01      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_11435,c_1832]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_601,plain,
% 11.81/2.01      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_341,c_5]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_26192,plain,
% 11.81/2.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_26070,c_601]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_30134,plain,
% 11.81/2.01      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_26192,c_10245]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_14322,plain,
% 11.81/2.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_9937,c_4]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_30204,plain,
% 11.81/2.01      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 11.81/2.01      inference(light_normalisation,[status(thm)],[c_30134,c_14322]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_8074,plain,
% 11.81/2.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X2,X1))) = k1_xboole_0 ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_0,c_4354]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_10373,plain,
% 11.81/2.01      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_10151,c_8074]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_15620,plain,
% 11.81/2.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k1_xboole_0),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_10373,c_10606]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_15736,plain,
% 11.81/2.01      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,X0) ),
% 11.81/2.01      inference(demodulation,[status(thm)],[c_15620,c_14322]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_30205,plain,
% 11.81/2.01      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 11.81/2.01      inference(demodulation,[status(thm)],[c_30204,c_15736]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_30455,plain,
% 11.81/2.01      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X1) ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_1,c_30205]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_30862,plain,
% 11.81/2.01      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = X1 ),
% 11.81/2.01      inference(demodulation,[status(thm)],[c_30455,c_10597]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_36899,plain,
% 11.81/2.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X1,X0),X2))),k1_xboole_0) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_12032,c_30862]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_14277,plain,
% 11.81/2.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X1,X0),X2))) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_9937,c_1334]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_37099,plain,
% 11.81/2.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k1_xboole_0) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 11.81/2.01      inference(light_normalisation,[status(thm)],[c_36899,c_14277]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_51139,plain,
% 11.81/2.01      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 11.81/2.01      inference(demodulation,[status(thm)],[c_51138,c_26501,c_37099]) ).
% 11.81/2.01  
% 11.81/2.01  cnf(c_52371,plain,
% 11.81/2.01      ( $false ),
% 11.81/2.01      inference(superposition,[status(thm)],[c_1,c_51139]) ).
% 11.81/2.01  
% 11.81/2.01  
% 11.81/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 11.81/2.01  
% 11.81/2.01  ------                               Statistics
% 11.81/2.01  
% 11.81/2.01  ------ General
% 11.81/2.01  
% 11.81/2.01  abstr_ref_over_cycles:                  0
% 11.81/2.01  abstr_ref_under_cycles:                 0
% 11.81/2.01  gc_basic_clause_elim:                   0
% 11.81/2.01  forced_gc_time:                         0
% 11.81/2.01  parsing_time:                           0.01
% 11.81/2.01  unif_index_cands_time:                  0.
% 11.81/2.01  unif_index_add_time:                    0.
% 11.81/2.01  orderings_time:                         0.
% 11.81/2.01  out_proof_time:                         0.008
% 11.81/2.01  total_time:                             1.45
% 11.81/2.01  num_of_symbols:                         37
% 11.81/2.01  num_of_terms:                           76705
% 11.81/2.01  
% 11.81/2.01  ------ Preprocessing
% 11.81/2.01  
% 11.81/2.01  num_of_splits:                          0
% 11.81/2.01  num_of_split_atoms:                     1
% 11.81/2.01  num_of_reused_defs:                     2
% 11.81/2.01  num_eq_ax_congr_red:                    0
% 11.81/2.01  num_of_sem_filtered_clauses:            0
% 11.81/2.01  num_of_subtypes:                        0
% 11.81/2.01  monotx_restored_types:                  0
% 11.81/2.01  sat_num_of_epr_types:                   0
% 11.81/2.01  sat_num_of_non_cyclic_types:            0
% 11.81/2.01  sat_guarded_non_collapsed_types:        0
% 11.81/2.01  num_pure_diseq_elim:                    0
% 11.81/2.01  simp_replaced_by:                       0
% 11.81/2.01  res_preprocessed:                       20
% 11.81/2.01  prep_upred:                             0
% 11.81/2.01  prep_unflattend:                        0
% 11.81/2.01  smt_new_axioms:                         0
% 11.81/2.01  pred_elim_cands:                        0
% 11.81/2.01  pred_elim:                              0
% 11.81/2.01  pred_elim_cl:                           0
% 11.81/2.01  pred_elim_cycles:                       0
% 11.81/2.01  merged_defs:                            0
% 11.81/2.01  merged_defs_ncl:                        0
% 11.81/2.01  bin_hyper_res:                          0
% 11.81/2.01  prep_cycles:                            2
% 11.81/2.01  pred_elim_time:                         0.
% 11.81/2.01  splitting_time:                         0.
% 11.81/2.01  sem_filter_time:                        0.
% 11.81/2.01  monotx_time:                            0.
% 11.81/2.01  subtype_inf_time:                       0.
% 11.81/2.01  
% 11.81/2.01  ------ Problem properties
% 11.81/2.01  
% 11.81/2.01  clauses:                                8
% 11.81/2.01  conjectures:                            1
% 11.81/2.01  epr:                                    0
% 11.81/2.01  horn:                                   8
% 11.81/2.01  ground:                                 1
% 11.81/2.01  unary:                                  8
% 11.81/2.01  binary:                                 0
% 11.81/2.01  lits:                                   8
% 11.81/2.01  lits_eq:                                8
% 11.81/2.01  fd_pure:                                0
% 11.81/2.01  fd_pseudo:                              0
% 11.81/2.01  fd_cond:                                0
% 11.81/2.01  fd_pseudo_cond:                         0
% 11.81/2.01  ac_symbols:                             1
% 11.81/2.01  
% 11.81/2.01  ------ Propositional Solver
% 11.81/2.01  
% 11.81/2.01  prop_solver_calls:                      13
% 11.81/2.01  prop_fast_solver_calls:                 52
% 11.81/2.01  smt_solver_calls:                       0
% 11.81/2.01  smt_fast_solver_calls:                  0
% 11.81/2.01  prop_num_of_clauses:                    340
% 11.81/2.01  prop_preprocess_simplified:             344
% 11.81/2.01  prop_fo_subsumed:                       0
% 11.81/2.01  prop_solver_time:                       0.
% 11.81/2.01  smt_solver_time:                        0.
% 11.81/2.01  smt_fast_solver_time:                   0.
% 11.81/2.01  prop_fast_solver_time:                  0.
% 11.81/2.01  prop_unsat_core_time:                   0.
% 11.81/2.01  
% 11.81/2.01  ------ QBF
% 11.81/2.01  
% 11.81/2.01  qbf_q_res:                              0
% 11.81/2.01  qbf_num_tautologies:                    0
% 11.81/2.01  qbf_prep_cycles:                        0
% 11.81/2.01  
% 11.81/2.01  ------ BMC1
% 11.81/2.01  
% 11.81/2.01  bmc1_current_bound:                     -1
% 11.81/2.01  bmc1_last_solved_bound:                 -1
% 11.81/2.01  bmc1_unsat_core_size:                   -1
% 11.81/2.01  bmc1_unsat_core_parents_size:           -1
% 11.81/2.01  bmc1_merge_next_fun:                    0
% 11.81/2.01  bmc1_unsat_core_clauses_time:           0.
% 11.81/2.01  
% 11.81/2.01  ------ Instantiation
% 11.81/2.01  
% 11.81/2.01  inst_num_of_clauses:                    0
% 11.81/2.01  inst_num_in_passive:                    0
% 11.81/2.01  inst_num_in_active:                     0
% 11.81/2.01  inst_num_in_unprocessed:                0
% 11.81/2.01  inst_num_of_loops:                      0
% 11.81/2.01  inst_num_of_learning_restarts:          0
% 11.81/2.01  inst_num_moves_active_passive:          0
% 11.81/2.01  inst_lit_activity:                      0
% 11.81/2.01  inst_lit_activity_moves:                0
% 11.81/2.01  inst_num_tautologies:                   0
% 11.81/2.01  inst_num_prop_implied:                  0
% 11.81/2.01  inst_num_existing_simplified:           0
% 11.81/2.01  inst_num_eq_res_simplified:             0
% 11.81/2.01  inst_num_child_elim:                    0
% 11.81/2.01  inst_num_of_dismatching_blockings:      0
% 11.81/2.01  inst_num_of_non_proper_insts:           0
% 11.81/2.01  inst_num_of_duplicates:                 0
% 11.81/2.01  inst_inst_num_from_inst_to_res:         0
% 11.81/2.01  inst_dismatching_checking_time:         0.
% 11.81/2.01  
% 11.81/2.01  ------ Resolution
% 11.81/2.01  
% 11.81/2.01  res_num_of_clauses:                     0
% 11.81/2.01  res_num_in_passive:                     0
% 11.81/2.01  res_num_in_active:                      0
% 11.81/2.01  res_num_of_loops:                       22
% 11.81/2.01  res_forward_subset_subsumed:            0
% 11.81/2.01  res_backward_subset_subsumed:           0
% 11.81/2.01  res_forward_subsumed:                   0
% 11.81/2.01  res_backward_subsumed:                  0
% 11.81/2.01  res_forward_subsumption_resolution:     0
% 11.81/2.01  res_backward_subsumption_resolution:    0
% 11.81/2.01  res_clause_to_clause_subsumption:       138665
% 11.81/2.01  res_orphan_elimination:                 0
% 11.81/2.01  res_tautology_del:                      0
% 11.81/2.01  res_num_eq_res_simplified:              0
% 11.81/2.01  res_num_sel_changes:                    0
% 11.81/2.01  res_moves_from_active_to_pass:          0
% 11.81/2.01  
% 11.81/2.01  ------ Superposition
% 11.81/2.01  
% 11.81/2.01  sup_time_total:                         0.
% 11.81/2.01  sup_time_generating:                    0.
% 11.81/2.01  sup_time_sim_full:                      0.
% 11.81/2.01  sup_time_sim_immed:                     0.
% 11.81/2.01  
% 11.81/2.01  sup_num_of_clauses:                     4919
% 11.81/2.01  sup_num_in_active:                      142
% 11.81/2.01  sup_num_in_passive:                     4777
% 11.81/2.01  sup_num_of_loops:                       202
% 11.81/2.01  sup_fw_superposition:                   18378
% 11.81/2.01  sup_bw_superposition:                   16916
% 11.81/2.01  sup_immediate_simplified:               15445
% 11.81/2.01  sup_given_eliminated:                   10
% 11.81/2.01  comparisons_done:                       0
% 11.81/2.01  comparisons_avoided:                    0
% 11.81/2.01  
% 11.81/2.01  ------ Simplifications
% 11.81/2.01  
% 11.81/2.01  
% 11.81/2.01  sim_fw_subset_subsumed:                 0
% 11.81/2.01  sim_bw_subset_subsumed:                 0
% 11.81/2.01  sim_fw_subsumed:                        3050
% 11.81/2.01  sim_bw_subsumed:                        86
% 11.81/2.01  sim_fw_subsumption_res:                 0
% 11.81/2.01  sim_bw_subsumption_res:                 0
% 11.81/2.01  sim_tautology_del:                      0
% 11.81/2.01  sim_eq_tautology_del:                   5186
% 11.81/2.01  sim_eq_res_simp:                        0
% 11.81/2.01  sim_fw_demodulated:                     10969
% 11.81/2.01  sim_bw_demodulated:                     175
% 11.81/2.01  sim_light_normalised:                   5741
% 11.81/2.01  sim_joinable_taut:                      22
% 11.81/2.01  sim_joinable_simp:                      0
% 11.81/2.01  sim_ac_normalised:                      0
% 11.81/2.01  sim_smt_subsumption:                    0
% 11.81/2.01  
%------------------------------------------------------------------------------
