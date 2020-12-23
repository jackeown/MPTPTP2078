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
% DateTime   : Thu Dec  3 11:24:59 EST 2020

% Result     : Theorem 7.49s
% Output     : CNFRefutation 7.49s
% Verified   : 
% Statistics : Number of formulae       :  121 (3049 expanded)
%              Number of clauses        :   91 (1395 expanded)
%              Number of leaves         :   12 ( 694 expanded)
%              Depth                    :   28
%              Number of atoms          :  134 (3134 expanded)
%              Number of equality atoms :  117 (3021 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f11,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f15,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f17,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17])).

fof(f30,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f31,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f30,f20,f20,f25])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_5,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_572,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_5])).

cnf(c_684,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_572])).

cnf(c_713,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_572,c_684])).

cnf(c_734,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_713,c_1])).

cnf(c_838,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_734])).

cnf(c_256,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_1065,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1,c_256])).

cnf(c_1141,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_838,c_1065])).

cnf(c_1143,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1065,c_734])).

cnf(c_1174,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1143,c_1065])).

cnf(c_1177,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_1141,c_1174])).

cnf(c_1343,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_3,c_1177])).

cnf(c_1397,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_1343,c_1177])).

cnf(c_2476,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1397,c_0])).

cnf(c_1146,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_1065,c_684])).

cnf(c_1168,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_1146,c_838])).

cnf(c_3400,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_2476,c_1168])).

cnf(c_3508,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_3400,c_1168])).

cnf(c_6,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_223,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_224,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_13246,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_223,c_224])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_221,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_13893,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_13246,c_221])).

cnf(c_4,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_14184,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_13893,c_4])).

cnf(c_15963,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_3508,c_14184])).

cnf(c_1133,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_3,c_1065])).

cnf(c_1188,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_1133,c_3])).

cnf(c_3791,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X0),X0) = k2_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1,c_1188])).

cnf(c_3945,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X0),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3791,c_1])).

cnf(c_257,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_3999,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_3945,c_257])).

cnf(c_15971,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0)),X2)) = k4_xboole_0(X0,k2_xboole_0(X2,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_3999,c_14184])).

cnf(c_16146,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X0))),X2)) = k4_xboole_0(X0,k2_xboole_0(X2,k4_xboole_0(X1,X0))) ),
    inference(demodulation,[status(thm)],[c_15971,c_4])).

cnf(c_16147,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X1,X0)),X2)) = k4_xboole_0(X0,k2_xboole_0(X2,k4_xboole_0(X1,X0))) ),
    inference(light_normalisation,[status(thm)],[c_16146,c_2476])).

cnf(c_16161,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X2,X2),X1)) ),
    inference(demodulation,[status(thm)],[c_15963,c_16147])).

cnf(c_3995,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_3945,c_0])).

cnf(c_4168,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_3995,c_5])).

cnf(c_15972,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0)),X2)) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) ),
    inference(superposition,[status(thm)],[c_4168,c_14184])).

cnf(c_16140,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0)),X2)) = k4_xboole_0(X0,X2) ),
    inference(light_normalisation,[status(thm)],[c_15972,c_14184])).

cnf(c_16142,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X0))),X2)) = k4_xboole_0(X0,X2) ),
    inference(demodulation,[status(thm)],[c_16140,c_4])).

cnf(c_16143,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X1,X0)),X2)) = k4_xboole_0(X0,X2) ),
    inference(light_normalisation,[status(thm)],[c_16142,c_2476])).

cnf(c_16162,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X1),X2)) = k4_xboole_0(X0,X2) ),
    inference(demodulation,[status(thm)],[c_15963,c_16143])).

cnf(c_16178,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_16161,c_16162])).

cnf(c_9,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_80,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
    inference(theory_normalisation,[status(thm)],[c_9,c_5,c_0])).

cnf(c_249,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_80,c_4])).

cnf(c_682,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_572,c_249])).

cnf(c_43410,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_16178,c_682])).

cnf(c_847,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_734,c_5])).

cnf(c_854,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_847,c_5])).

cnf(c_27039,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k2_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(k2_xboole_0(X0,X1),X2)) ),
    inference(superposition,[status(thm)],[c_1168,c_854])).

cnf(c_27165,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X2),X3)) = k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_854,c_5])).

cnf(c_1360,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1177,c_1065])).

cnf(c_1381,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_1360,c_1177])).

cnf(c_27040,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(k2_xboole_0(X0,X1),X2)) ),
    inference(superposition,[status(thm)],[c_1381,c_854])).

cnf(c_27043,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_838,c_854])).

cnf(c_258,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_4010,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X0))) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_3945,c_258])).

cnf(c_27064,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X0)),X2)) = k2_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_4010,c_854])).

cnf(c_15964,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1397,c_14184])).

cnf(c_391,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_4,c_3])).

cnf(c_18759,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_15964,c_391])).

cnf(c_18772,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_18759,c_3995])).

cnf(c_19099,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_18772,c_5])).

cnf(c_21467,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)),X2)) = k2_xboole_0(X0,k2_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_3999,c_19099])).

cnf(c_21742,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_21467,c_4,c_19099])).

cnf(c_27074,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X2)),X3)) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X3)) ),
    inference(superposition,[status(thm)],[c_21742,c_854])).

cnf(c_27179,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_854,c_0])).

cnf(c_27533,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X2)),X3)) = k2_xboole_0(X0,k2_xboole_0(X3,X1)) ),
    inference(demodulation,[status(thm)],[c_27074,c_27179])).

cnf(c_27552,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(demodulation,[status(thm)],[c_27064,c_27533])).

cnf(c_27586,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(demodulation,[status(thm)],[c_27043,c_27552])).

cnf(c_27589,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(light_normalisation,[status(thm)],[c_27040,c_27586])).

cnf(c_27592,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X1)),X2) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(demodulation,[status(thm)],[c_27039,c_27165,c_27589])).

cnf(c_27594,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X2),X1) ),
    inference(demodulation,[status(thm)],[c_27592,c_1])).

cnf(c_43411,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_43410,c_2476,c_27594])).

cnf(c_573,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_3,c_5])).

cnf(c_585,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_573,c_5])).

cnf(c_3817,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1188,c_1177])).

cnf(c_3827,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1188,c_684])).

cnf(c_3875,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_3827,c_1168])).

cnf(c_3889,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_3817,c_3875])).

cnf(c_43412,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_43411,c_585,c_2476,c_3889])).

cnf(c_43413,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_43412])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:32:08 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.49/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.49/1.49  
% 7.49/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.49/1.49  
% 7.49/1.49  ------  iProver source info
% 7.49/1.49  
% 7.49/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.49/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.49/1.49  git: non_committed_changes: false
% 7.49/1.49  git: last_make_outside_of_git: false
% 7.49/1.49  
% 7.49/1.49  ------ 
% 7.49/1.49  
% 7.49/1.49  ------ Input Options
% 7.49/1.49  
% 7.49/1.49  --out_options                           all
% 7.49/1.49  --tptp_safe_out                         true
% 7.49/1.49  --problem_path                          ""
% 7.49/1.49  --include_path                          ""
% 7.49/1.49  --clausifier                            res/vclausify_rel
% 7.49/1.49  --clausifier_options                    --mode clausify
% 7.49/1.49  --stdin                                 false
% 7.49/1.49  --stats_out                             all
% 7.49/1.49  
% 7.49/1.49  ------ General Options
% 7.49/1.49  
% 7.49/1.49  --fof                                   false
% 7.49/1.49  --time_out_real                         305.
% 7.49/1.49  --time_out_virtual                      -1.
% 7.49/1.49  --symbol_type_check                     false
% 7.49/1.49  --clausify_out                          false
% 7.49/1.49  --sig_cnt_out                           false
% 7.49/1.50  --trig_cnt_out                          false
% 7.49/1.50  --trig_cnt_out_tolerance                1.
% 7.49/1.50  --trig_cnt_out_sk_spl                   false
% 7.49/1.50  --abstr_cl_out                          false
% 7.49/1.50  
% 7.49/1.50  ------ Global Options
% 7.49/1.50  
% 7.49/1.50  --schedule                              default
% 7.49/1.50  --add_important_lit                     false
% 7.49/1.50  --prop_solver_per_cl                    1000
% 7.49/1.50  --min_unsat_core                        false
% 7.49/1.50  --soft_assumptions                      false
% 7.49/1.50  --soft_lemma_size                       3
% 7.49/1.50  --prop_impl_unit_size                   0
% 7.49/1.50  --prop_impl_unit                        []
% 7.49/1.50  --share_sel_clauses                     true
% 7.49/1.50  --reset_solvers                         false
% 7.49/1.50  --bc_imp_inh                            [conj_cone]
% 7.49/1.50  --conj_cone_tolerance                   3.
% 7.49/1.50  --extra_neg_conj                        none
% 7.49/1.50  --large_theory_mode                     true
% 7.49/1.50  --prolific_symb_bound                   200
% 7.49/1.50  --lt_threshold                          2000
% 7.49/1.50  --clause_weak_htbl                      true
% 7.49/1.50  --gc_record_bc_elim                     false
% 7.49/1.50  
% 7.49/1.50  ------ Preprocessing Options
% 7.49/1.50  
% 7.49/1.50  --preprocessing_flag                    true
% 7.49/1.50  --time_out_prep_mult                    0.1
% 7.49/1.50  --splitting_mode                        input
% 7.49/1.50  --splitting_grd                         true
% 7.49/1.50  --splitting_cvd                         false
% 7.49/1.50  --splitting_cvd_svl                     false
% 7.49/1.50  --splitting_nvd                         32
% 7.49/1.50  --sub_typing                            true
% 7.49/1.50  --prep_gs_sim                           true
% 7.49/1.50  --prep_unflatten                        true
% 7.49/1.50  --prep_res_sim                          true
% 7.49/1.50  --prep_upred                            true
% 7.49/1.50  --prep_sem_filter                       exhaustive
% 7.49/1.50  --prep_sem_filter_out                   false
% 7.49/1.50  --pred_elim                             true
% 7.49/1.50  --res_sim_input                         true
% 7.49/1.50  --eq_ax_congr_red                       true
% 7.49/1.50  --pure_diseq_elim                       true
% 7.49/1.50  --brand_transform                       false
% 7.49/1.50  --non_eq_to_eq                          false
% 7.49/1.50  --prep_def_merge                        true
% 7.49/1.50  --prep_def_merge_prop_impl              false
% 7.49/1.50  --prep_def_merge_mbd                    true
% 7.49/1.50  --prep_def_merge_tr_red                 false
% 7.49/1.50  --prep_def_merge_tr_cl                  false
% 7.49/1.50  --smt_preprocessing                     true
% 7.49/1.50  --smt_ac_axioms                         fast
% 7.49/1.50  --preprocessed_out                      false
% 7.49/1.50  --preprocessed_stats                    false
% 7.49/1.50  
% 7.49/1.50  ------ Abstraction refinement Options
% 7.49/1.50  
% 7.49/1.50  --abstr_ref                             []
% 7.49/1.50  --abstr_ref_prep                        false
% 7.49/1.50  --abstr_ref_until_sat                   false
% 7.49/1.50  --abstr_ref_sig_restrict                funpre
% 7.49/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.49/1.50  --abstr_ref_under                       []
% 7.49/1.50  
% 7.49/1.50  ------ SAT Options
% 7.49/1.50  
% 7.49/1.50  --sat_mode                              false
% 7.49/1.50  --sat_fm_restart_options                ""
% 7.49/1.50  --sat_gr_def                            false
% 7.49/1.50  --sat_epr_types                         true
% 7.49/1.50  --sat_non_cyclic_types                  false
% 7.49/1.50  --sat_finite_models                     false
% 7.49/1.50  --sat_fm_lemmas                         false
% 7.49/1.50  --sat_fm_prep                           false
% 7.49/1.50  --sat_fm_uc_incr                        true
% 7.49/1.50  --sat_out_model                         small
% 7.49/1.50  --sat_out_clauses                       false
% 7.49/1.50  
% 7.49/1.50  ------ QBF Options
% 7.49/1.50  
% 7.49/1.50  --qbf_mode                              false
% 7.49/1.50  --qbf_elim_univ                         false
% 7.49/1.50  --qbf_dom_inst                          none
% 7.49/1.50  --qbf_dom_pre_inst                      false
% 7.49/1.50  --qbf_sk_in                             false
% 7.49/1.50  --qbf_pred_elim                         true
% 7.49/1.50  --qbf_split                             512
% 7.49/1.50  
% 7.49/1.50  ------ BMC1 Options
% 7.49/1.50  
% 7.49/1.50  --bmc1_incremental                      false
% 7.49/1.50  --bmc1_axioms                           reachable_all
% 7.49/1.50  --bmc1_min_bound                        0
% 7.49/1.50  --bmc1_max_bound                        -1
% 7.49/1.50  --bmc1_max_bound_default                -1
% 7.49/1.50  --bmc1_symbol_reachability              true
% 7.49/1.50  --bmc1_property_lemmas                  false
% 7.49/1.50  --bmc1_k_induction                      false
% 7.49/1.50  --bmc1_non_equiv_states                 false
% 7.49/1.50  --bmc1_deadlock                         false
% 7.49/1.50  --bmc1_ucm                              false
% 7.49/1.50  --bmc1_add_unsat_core                   none
% 7.49/1.50  --bmc1_unsat_core_children              false
% 7.49/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.49/1.50  --bmc1_out_stat                         full
% 7.49/1.50  --bmc1_ground_init                      false
% 7.49/1.50  --bmc1_pre_inst_next_state              false
% 7.49/1.50  --bmc1_pre_inst_state                   false
% 7.49/1.50  --bmc1_pre_inst_reach_state             false
% 7.49/1.50  --bmc1_out_unsat_core                   false
% 7.49/1.50  --bmc1_aig_witness_out                  false
% 7.49/1.50  --bmc1_verbose                          false
% 7.49/1.50  --bmc1_dump_clauses_tptp                false
% 7.49/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.49/1.50  --bmc1_dump_file                        -
% 7.49/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.49/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.49/1.50  --bmc1_ucm_extend_mode                  1
% 7.49/1.50  --bmc1_ucm_init_mode                    2
% 7.49/1.50  --bmc1_ucm_cone_mode                    none
% 7.49/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.49/1.50  --bmc1_ucm_relax_model                  4
% 7.49/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.49/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.49/1.50  --bmc1_ucm_layered_model                none
% 7.49/1.50  --bmc1_ucm_max_lemma_size               10
% 7.49/1.50  
% 7.49/1.50  ------ AIG Options
% 7.49/1.50  
% 7.49/1.50  --aig_mode                              false
% 7.49/1.50  
% 7.49/1.50  ------ Instantiation Options
% 7.49/1.50  
% 7.49/1.50  --instantiation_flag                    true
% 7.49/1.50  --inst_sos_flag                         false
% 7.49/1.50  --inst_sos_phase                        true
% 7.49/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.49/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.49/1.50  --inst_lit_sel_side                     num_symb
% 7.49/1.50  --inst_solver_per_active                1400
% 7.49/1.50  --inst_solver_calls_frac                1.
% 7.49/1.50  --inst_passive_queue_type               priority_queues
% 7.49/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.49/1.50  --inst_passive_queues_freq              [25;2]
% 7.49/1.50  --inst_dismatching                      true
% 7.49/1.50  --inst_eager_unprocessed_to_passive     true
% 7.49/1.50  --inst_prop_sim_given                   true
% 7.49/1.50  --inst_prop_sim_new                     false
% 7.49/1.50  --inst_subs_new                         false
% 7.49/1.50  --inst_eq_res_simp                      false
% 7.49/1.50  --inst_subs_given                       false
% 7.49/1.50  --inst_orphan_elimination               true
% 7.49/1.50  --inst_learning_loop_flag               true
% 7.49/1.50  --inst_learning_start                   3000
% 7.49/1.50  --inst_learning_factor                  2
% 7.49/1.50  --inst_start_prop_sim_after_learn       3
% 7.49/1.50  --inst_sel_renew                        solver
% 7.49/1.50  --inst_lit_activity_flag                true
% 7.49/1.50  --inst_restr_to_given                   false
% 7.49/1.50  --inst_activity_threshold               500
% 7.49/1.50  --inst_out_proof                        true
% 7.49/1.50  
% 7.49/1.50  ------ Resolution Options
% 7.49/1.50  
% 7.49/1.50  --resolution_flag                       true
% 7.49/1.50  --res_lit_sel                           adaptive
% 7.49/1.50  --res_lit_sel_side                      none
% 7.49/1.50  --res_ordering                          kbo
% 7.49/1.50  --res_to_prop_solver                    active
% 7.49/1.50  --res_prop_simpl_new                    false
% 7.49/1.50  --res_prop_simpl_given                  true
% 7.49/1.50  --res_passive_queue_type                priority_queues
% 7.49/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.49/1.50  --res_passive_queues_freq               [15;5]
% 7.49/1.50  --res_forward_subs                      full
% 7.49/1.50  --res_backward_subs                     full
% 7.49/1.50  --res_forward_subs_resolution           true
% 7.49/1.50  --res_backward_subs_resolution          true
% 7.49/1.50  --res_orphan_elimination                true
% 7.49/1.50  --res_time_limit                        2.
% 7.49/1.50  --res_out_proof                         true
% 7.49/1.50  
% 7.49/1.50  ------ Superposition Options
% 7.49/1.50  
% 7.49/1.50  --superposition_flag                    true
% 7.49/1.50  --sup_passive_queue_type                priority_queues
% 7.49/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.49/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.49/1.50  --demod_completeness_check              fast
% 7.49/1.50  --demod_use_ground                      true
% 7.49/1.50  --sup_to_prop_solver                    passive
% 7.49/1.50  --sup_prop_simpl_new                    true
% 7.49/1.50  --sup_prop_simpl_given                  true
% 7.49/1.50  --sup_fun_splitting                     false
% 7.49/1.50  --sup_smt_interval                      50000
% 7.49/1.50  
% 7.49/1.50  ------ Superposition Simplification Setup
% 7.49/1.50  
% 7.49/1.50  --sup_indices_passive                   []
% 7.49/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.49/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.49/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.49/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.49/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.49/1.50  --sup_full_bw                           [BwDemod]
% 7.49/1.50  --sup_immed_triv                        [TrivRules]
% 7.49/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.49/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.49/1.50  --sup_immed_bw_main                     []
% 7.49/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.49/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.49/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.49/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.49/1.50  
% 7.49/1.50  ------ Combination Options
% 7.49/1.50  
% 7.49/1.50  --comb_res_mult                         3
% 7.49/1.50  --comb_sup_mult                         2
% 7.49/1.50  --comb_inst_mult                        10
% 7.49/1.50  
% 7.49/1.50  ------ Debug Options
% 7.49/1.50  
% 7.49/1.50  --dbg_backtrace                         false
% 7.49/1.50  --dbg_dump_prop_clauses                 false
% 7.49/1.50  --dbg_dump_prop_clauses_file            -
% 7.49/1.50  --dbg_out_stat                          false
% 7.49/1.50  ------ Parsing...
% 7.49/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.49/1.50  
% 7.49/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.49/1.50  
% 7.49/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.49/1.50  
% 7.49/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.49/1.50  ------ Proving...
% 7.49/1.50  ------ Problem Properties 
% 7.49/1.50  
% 7.49/1.50  
% 7.49/1.50  clauses                                 10
% 7.49/1.50  conjectures                             1
% 7.49/1.50  EPR                                     1
% 7.49/1.50  Horn                                    10
% 7.49/1.50  unary                                   7
% 7.49/1.50  binary                                  3
% 7.49/1.50  lits                                    13
% 7.49/1.50  lits eq                                 8
% 7.49/1.50  fd_pure                                 0
% 7.49/1.50  fd_pseudo                               0
% 7.49/1.50  fd_cond                                 0
% 7.49/1.50  fd_pseudo_cond                          0
% 7.49/1.50  AC symbols                              1
% 7.49/1.50  
% 7.49/1.50  ------ Schedule dynamic 5 is on 
% 7.49/1.50  
% 7.49/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.49/1.50  
% 7.49/1.50  
% 7.49/1.50  ------ 
% 7.49/1.50  Current options:
% 7.49/1.50  ------ 
% 7.49/1.50  
% 7.49/1.50  ------ Input Options
% 7.49/1.50  
% 7.49/1.50  --out_options                           all
% 7.49/1.50  --tptp_safe_out                         true
% 7.49/1.50  --problem_path                          ""
% 7.49/1.50  --include_path                          ""
% 7.49/1.50  --clausifier                            res/vclausify_rel
% 7.49/1.50  --clausifier_options                    --mode clausify
% 7.49/1.50  --stdin                                 false
% 7.49/1.50  --stats_out                             all
% 7.49/1.50  
% 7.49/1.50  ------ General Options
% 7.49/1.50  
% 7.49/1.50  --fof                                   false
% 7.49/1.50  --time_out_real                         305.
% 7.49/1.50  --time_out_virtual                      -1.
% 7.49/1.50  --symbol_type_check                     false
% 7.49/1.50  --clausify_out                          false
% 7.49/1.50  --sig_cnt_out                           false
% 7.49/1.50  --trig_cnt_out                          false
% 7.49/1.50  --trig_cnt_out_tolerance                1.
% 7.49/1.50  --trig_cnt_out_sk_spl                   false
% 7.49/1.50  --abstr_cl_out                          false
% 7.49/1.50  
% 7.49/1.50  ------ Global Options
% 7.49/1.50  
% 7.49/1.50  --schedule                              default
% 7.49/1.50  --add_important_lit                     false
% 7.49/1.50  --prop_solver_per_cl                    1000
% 7.49/1.50  --min_unsat_core                        false
% 7.49/1.50  --soft_assumptions                      false
% 7.49/1.50  --soft_lemma_size                       3
% 7.49/1.50  --prop_impl_unit_size                   0
% 7.49/1.50  --prop_impl_unit                        []
% 7.49/1.50  --share_sel_clauses                     true
% 7.49/1.50  --reset_solvers                         false
% 7.49/1.50  --bc_imp_inh                            [conj_cone]
% 7.49/1.50  --conj_cone_tolerance                   3.
% 7.49/1.50  --extra_neg_conj                        none
% 7.49/1.50  --large_theory_mode                     true
% 7.49/1.50  --prolific_symb_bound                   200
% 7.49/1.50  --lt_threshold                          2000
% 7.49/1.50  --clause_weak_htbl                      true
% 7.49/1.50  --gc_record_bc_elim                     false
% 7.49/1.50  
% 7.49/1.50  ------ Preprocessing Options
% 7.49/1.50  
% 7.49/1.50  --preprocessing_flag                    true
% 7.49/1.50  --time_out_prep_mult                    0.1
% 7.49/1.50  --splitting_mode                        input
% 7.49/1.50  --splitting_grd                         true
% 7.49/1.50  --splitting_cvd                         false
% 7.49/1.50  --splitting_cvd_svl                     false
% 7.49/1.50  --splitting_nvd                         32
% 7.49/1.50  --sub_typing                            true
% 7.49/1.50  --prep_gs_sim                           true
% 7.49/1.50  --prep_unflatten                        true
% 7.49/1.50  --prep_res_sim                          true
% 7.49/1.50  --prep_upred                            true
% 7.49/1.50  --prep_sem_filter                       exhaustive
% 7.49/1.50  --prep_sem_filter_out                   false
% 7.49/1.50  --pred_elim                             true
% 7.49/1.50  --res_sim_input                         true
% 7.49/1.50  --eq_ax_congr_red                       true
% 7.49/1.50  --pure_diseq_elim                       true
% 7.49/1.50  --brand_transform                       false
% 7.49/1.50  --non_eq_to_eq                          false
% 7.49/1.50  --prep_def_merge                        true
% 7.49/1.50  --prep_def_merge_prop_impl              false
% 7.49/1.50  --prep_def_merge_mbd                    true
% 7.49/1.50  --prep_def_merge_tr_red                 false
% 7.49/1.50  --prep_def_merge_tr_cl                  false
% 7.49/1.50  --smt_preprocessing                     true
% 7.49/1.50  --smt_ac_axioms                         fast
% 7.49/1.50  --preprocessed_out                      false
% 7.49/1.50  --preprocessed_stats                    false
% 7.49/1.50  
% 7.49/1.50  ------ Abstraction refinement Options
% 7.49/1.50  
% 7.49/1.50  --abstr_ref                             []
% 7.49/1.50  --abstr_ref_prep                        false
% 7.49/1.50  --abstr_ref_until_sat                   false
% 7.49/1.50  --abstr_ref_sig_restrict                funpre
% 7.49/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.49/1.50  --abstr_ref_under                       []
% 7.49/1.50  
% 7.49/1.50  ------ SAT Options
% 7.49/1.50  
% 7.49/1.50  --sat_mode                              false
% 7.49/1.50  --sat_fm_restart_options                ""
% 7.49/1.50  --sat_gr_def                            false
% 7.49/1.50  --sat_epr_types                         true
% 7.49/1.50  --sat_non_cyclic_types                  false
% 7.49/1.50  --sat_finite_models                     false
% 7.49/1.50  --sat_fm_lemmas                         false
% 7.49/1.50  --sat_fm_prep                           false
% 7.49/1.50  --sat_fm_uc_incr                        true
% 7.49/1.50  --sat_out_model                         small
% 7.49/1.50  --sat_out_clauses                       false
% 7.49/1.50  
% 7.49/1.50  ------ QBF Options
% 7.49/1.50  
% 7.49/1.50  --qbf_mode                              false
% 7.49/1.50  --qbf_elim_univ                         false
% 7.49/1.50  --qbf_dom_inst                          none
% 7.49/1.50  --qbf_dom_pre_inst                      false
% 7.49/1.50  --qbf_sk_in                             false
% 7.49/1.50  --qbf_pred_elim                         true
% 7.49/1.50  --qbf_split                             512
% 7.49/1.50  
% 7.49/1.50  ------ BMC1 Options
% 7.49/1.50  
% 7.49/1.50  --bmc1_incremental                      false
% 7.49/1.50  --bmc1_axioms                           reachable_all
% 7.49/1.50  --bmc1_min_bound                        0
% 7.49/1.50  --bmc1_max_bound                        -1
% 7.49/1.50  --bmc1_max_bound_default                -1
% 7.49/1.50  --bmc1_symbol_reachability              true
% 7.49/1.50  --bmc1_property_lemmas                  false
% 7.49/1.50  --bmc1_k_induction                      false
% 7.49/1.50  --bmc1_non_equiv_states                 false
% 7.49/1.50  --bmc1_deadlock                         false
% 7.49/1.50  --bmc1_ucm                              false
% 7.49/1.50  --bmc1_add_unsat_core                   none
% 7.49/1.50  --bmc1_unsat_core_children              false
% 7.49/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.49/1.50  --bmc1_out_stat                         full
% 7.49/1.50  --bmc1_ground_init                      false
% 7.49/1.50  --bmc1_pre_inst_next_state              false
% 7.49/1.50  --bmc1_pre_inst_state                   false
% 7.49/1.50  --bmc1_pre_inst_reach_state             false
% 7.49/1.50  --bmc1_out_unsat_core                   false
% 7.49/1.50  --bmc1_aig_witness_out                  false
% 7.49/1.50  --bmc1_verbose                          false
% 7.49/1.50  --bmc1_dump_clauses_tptp                false
% 7.49/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.49/1.50  --bmc1_dump_file                        -
% 7.49/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.49/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.49/1.50  --bmc1_ucm_extend_mode                  1
% 7.49/1.50  --bmc1_ucm_init_mode                    2
% 7.49/1.50  --bmc1_ucm_cone_mode                    none
% 7.49/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.49/1.50  --bmc1_ucm_relax_model                  4
% 7.49/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.49/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.49/1.50  --bmc1_ucm_layered_model                none
% 7.49/1.50  --bmc1_ucm_max_lemma_size               10
% 7.49/1.50  
% 7.49/1.50  ------ AIG Options
% 7.49/1.50  
% 7.49/1.50  --aig_mode                              false
% 7.49/1.50  
% 7.49/1.50  ------ Instantiation Options
% 7.49/1.50  
% 7.49/1.50  --instantiation_flag                    true
% 7.49/1.50  --inst_sos_flag                         false
% 7.49/1.50  --inst_sos_phase                        true
% 7.49/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.49/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.49/1.50  --inst_lit_sel_side                     none
% 7.49/1.50  --inst_solver_per_active                1400
% 7.49/1.50  --inst_solver_calls_frac                1.
% 7.49/1.50  --inst_passive_queue_type               priority_queues
% 7.49/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.49/1.50  --inst_passive_queues_freq              [25;2]
% 7.49/1.50  --inst_dismatching                      true
% 7.49/1.50  --inst_eager_unprocessed_to_passive     true
% 7.49/1.50  --inst_prop_sim_given                   true
% 7.49/1.50  --inst_prop_sim_new                     false
% 7.49/1.50  --inst_subs_new                         false
% 7.49/1.50  --inst_eq_res_simp                      false
% 7.49/1.50  --inst_subs_given                       false
% 7.49/1.50  --inst_orphan_elimination               true
% 7.49/1.50  --inst_learning_loop_flag               true
% 7.49/1.50  --inst_learning_start                   3000
% 7.49/1.50  --inst_learning_factor                  2
% 7.49/1.50  --inst_start_prop_sim_after_learn       3
% 7.49/1.50  --inst_sel_renew                        solver
% 7.49/1.50  --inst_lit_activity_flag                true
% 7.49/1.50  --inst_restr_to_given                   false
% 7.49/1.50  --inst_activity_threshold               500
% 7.49/1.50  --inst_out_proof                        true
% 7.49/1.50  
% 7.49/1.50  ------ Resolution Options
% 7.49/1.50  
% 7.49/1.50  --resolution_flag                       false
% 7.49/1.50  --res_lit_sel                           adaptive
% 7.49/1.50  --res_lit_sel_side                      none
% 7.49/1.50  --res_ordering                          kbo
% 7.49/1.50  --res_to_prop_solver                    active
% 7.49/1.50  --res_prop_simpl_new                    false
% 7.49/1.50  --res_prop_simpl_given                  true
% 7.49/1.50  --res_passive_queue_type                priority_queues
% 7.49/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.49/1.50  --res_passive_queues_freq               [15;5]
% 7.49/1.50  --res_forward_subs                      full
% 7.49/1.50  --res_backward_subs                     full
% 7.49/1.50  --res_forward_subs_resolution           true
% 7.49/1.50  --res_backward_subs_resolution          true
% 7.49/1.50  --res_orphan_elimination                true
% 7.49/1.50  --res_time_limit                        2.
% 7.49/1.50  --res_out_proof                         true
% 7.49/1.50  
% 7.49/1.50  ------ Superposition Options
% 7.49/1.50  
% 7.49/1.50  --superposition_flag                    true
% 7.49/1.50  --sup_passive_queue_type                priority_queues
% 7.49/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.49/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.49/1.50  --demod_completeness_check              fast
% 7.49/1.50  --demod_use_ground                      true
% 7.49/1.50  --sup_to_prop_solver                    passive
% 7.49/1.50  --sup_prop_simpl_new                    true
% 7.49/1.50  --sup_prop_simpl_given                  true
% 7.49/1.50  --sup_fun_splitting                     false
% 7.49/1.50  --sup_smt_interval                      50000
% 7.49/1.50  
% 7.49/1.50  ------ Superposition Simplification Setup
% 7.49/1.50  
% 7.49/1.50  --sup_indices_passive                   []
% 7.49/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.49/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.49/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.49/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.49/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.49/1.50  --sup_full_bw                           [BwDemod]
% 7.49/1.50  --sup_immed_triv                        [TrivRules]
% 7.49/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.49/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.49/1.50  --sup_immed_bw_main                     []
% 7.49/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.49/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.49/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.49/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.49/1.50  
% 7.49/1.50  ------ Combination Options
% 7.49/1.50  
% 7.49/1.50  --comb_res_mult                         3
% 7.49/1.50  --comb_sup_mult                         2
% 7.49/1.50  --comb_inst_mult                        10
% 7.49/1.50  
% 7.49/1.50  ------ Debug Options
% 7.49/1.50  
% 7.49/1.50  --dbg_backtrace                         false
% 7.49/1.50  --dbg_dump_prop_clauses                 false
% 7.49/1.50  --dbg_dump_prop_clauses_file            -
% 7.49/1.50  --dbg_out_stat                          false
% 7.49/1.50  
% 7.49/1.50  
% 7.49/1.50  
% 7.49/1.50  
% 7.49/1.50  ------ Proving...
% 7.49/1.50  
% 7.49/1.50  
% 7.49/1.50  % SZS status Theorem for theBenchmark.p
% 7.49/1.50  
% 7.49/1.50   Resolution empty clause
% 7.49/1.50  
% 7.49/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.49/1.50  
% 7.49/1.50  fof(f5,axiom,(
% 7.49/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.49/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.49/1.50  
% 7.49/1.50  fof(f23,plain,(
% 7.49/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.49/1.50    inference(cnf_transformation,[],[f5])).
% 7.49/1.50  
% 7.49/1.50  fof(f1,axiom,(
% 7.49/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.49/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.49/1.50  
% 7.49/1.50  fof(f19,plain,(
% 7.49/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f1])).
% 7.49/1.50  
% 7.49/1.50  fof(f3,axiom,(
% 7.49/1.50    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 7.49/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.49/1.50  
% 7.49/1.50  fof(f13,plain,(
% 7.49/1.50    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 7.49/1.50    inference(rectify,[],[f3])).
% 7.49/1.50  
% 7.49/1.50  fof(f21,plain,(
% 7.49/1.50    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 7.49/1.50    inference(cnf_transformation,[],[f13])).
% 7.49/1.50  
% 7.49/1.50  fof(f8,axiom,(
% 7.49/1.50    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 7.49/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.49/1.50  
% 7.49/1.50  fof(f26,plain,(
% 7.49/1.50    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f8])).
% 7.49/1.50  
% 7.49/1.50  fof(f9,axiom,(
% 7.49/1.50    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 7.49/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.49/1.50  
% 7.49/1.50  fof(f27,plain,(
% 7.49/1.50    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f9])).
% 7.49/1.50  
% 7.49/1.50  fof(f4,axiom,(
% 7.49/1.50    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 7.49/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.49/1.50  
% 7.49/1.50  fof(f14,plain,(
% 7.49/1.50    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 7.49/1.50    inference(ennf_transformation,[],[f4])).
% 7.49/1.50  
% 7.49/1.50  fof(f22,plain,(
% 7.49/1.50    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f14])).
% 7.49/1.50  
% 7.49/1.50  fof(f10,axiom,(
% 7.49/1.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 7.49/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.49/1.50  
% 7.49/1.50  fof(f16,plain,(
% 7.49/1.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 7.49/1.50    inference(nnf_transformation,[],[f10])).
% 7.49/1.50  
% 7.49/1.50  fof(f28,plain,(
% 7.49/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f16])).
% 7.49/1.50  
% 7.49/1.50  fof(f6,axiom,(
% 7.49/1.50    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 7.49/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.49/1.50  
% 7.49/1.50  fof(f24,plain,(
% 7.49/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f6])).
% 7.49/1.50  
% 7.49/1.50  fof(f11,conjecture,(
% 7.49/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 7.49/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.49/1.50  
% 7.49/1.50  fof(f12,negated_conjecture,(
% 7.49/1.50    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 7.49/1.50    inference(negated_conjecture,[],[f11])).
% 7.49/1.50  
% 7.49/1.50  fof(f15,plain,(
% 7.49/1.50    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 7.49/1.50    inference(ennf_transformation,[],[f12])).
% 7.49/1.50  
% 7.49/1.50  fof(f17,plain,(
% 7.49/1.50    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 7.49/1.50    introduced(choice_axiom,[])).
% 7.49/1.50  
% 7.49/1.50  fof(f18,plain,(
% 7.49/1.50    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 7.49/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17])).
% 7.49/1.50  
% 7.49/1.50  fof(f30,plain,(
% 7.49/1.50    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 7.49/1.50    inference(cnf_transformation,[],[f18])).
% 7.49/1.50  
% 7.49/1.50  fof(f2,axiom,(
% 7.49/1.50    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 7.49/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.49/1.50  
% 7.49/1.50  fof(f20,plain,(
% 7.49/1.50    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f2])).
% 7.49/1.50  
% 7.49/1.50  fof(f7,axiom,(
% 7.49/1.50    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 7.49/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.49/1.50  
% 7.49/1.50  fof(f25,plain,(
% 7.49/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f7])).
% 7.49/1.50  
% 7.49/1.50  fof(f31,plain,(
% 7.49/1.50    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 7.49/1.50    inference(definition_unfolding,[],[f30,f20,f20,f25])).
% 7.49/1.50  
% 7.49/1.50  cnf(c_3,plain,
% 7.49/1.50      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.49/1.50      inference(cnf_transformation,[],[f23]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_0,plain,
% 7.49/1.50      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 7.49/1.50      inference(cnf_transformation,[],[f19]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1,plain,
% 7.49/1.50      ( k2_xboole_0(X0,X0) = X0 ),
% 7.49/1.50      inference(cnf_transformation,[],[f21]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5,plain,
% 7.49/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.49/1.50      inference(cnf_transformation,[],[f26]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_572,plain,
% 7.49/1.50      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_1,c_5]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_684,plain,
% 7.49/1.50      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_0,c_572]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_713,plain,
% 7.49/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_572,c_684]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_734,plain,
% 7.49/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 7.49/1.50      inference(demodulation,[status(thm)],[c_713,c_1]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_838,plain,
% 7.49/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_0,c_734]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_256,plain,
% 7.49/1.50      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_5,c_0]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1065,plain,
% 7.49/1.50      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_1,c_256]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1141,plain,
% 7.49/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,k2_xboole_0(X1,X0)) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_838,c_1065]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1143,plain,
% 7.49/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_1065,c_734]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1174,plain,
% 7.49/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 7.49/1.50      inference(demodulation,[status(thm)],[c_1143,c_1065]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1177,plain,
% 7.49/1.50      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 7.49/1.50      inference(light_normalisation,[status(thm)],[c_1141,c_1174]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1343,plain,
% 7.49/1.50      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_3,c_1177]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1397,plain,
% 7.49/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 7.49/1.50      inference(light_normalisation,[status(thm)],[c_1343,c_1177]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_2476,plain,
% 7.49/1.50      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_1397,c_0]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1146,plain,
% 7.49/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X1) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_1065,c_684]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1168,plain,
% 7.49/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 7.49/1.50      inference(light_normalisation,[status(thm)],[c_1146,c_838]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_3400,plain,
% 7.49/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_2476,c_1168]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_3508,plain,
% 7.49/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 7.49/1.50      inference(light_normalisation,[status(thm)],[c_3400,c_1168]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_6,plain,
% 7.49/1.50      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 7.49/1.50      inference(cnf_transformation,[],[f27]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_223,plain,
% 7.49/1.50      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_2,plain,
% 7.49/1.50      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 7.49/1.50      inference(cnf_transformation,[],[f22]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_224,plain,
% 7.49/1.50      ( r1_xboole_0(X0,X1) != iProver_top | r1_xboole_0(X1,X0) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_13246,plain,
% 7.49/1.50      ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_223,c_224]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_8,plain,
% 7.49/1.50      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 7.49/1.50      inference(cnf_transformation,[],[f28]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_221,plain,
% 7.49/1.50      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_13893,plain,
% 7.49/1.50      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_13246,c_221]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_4,plain,
% 7.49/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.49/1.50      inference(cnf_transformation,[],[f24]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_14184,plain,
% 7.49/1.50      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_13893,c_4]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_15963,plain,
% 7.49/1.50      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(X0,X0) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_3508,c_14184]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1133,plain,
% 7.49/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_3,c_1065]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1188,plain,
% 7.49/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 7.49/1.50      inference(demodulation,[status(thm)],[c_1133,c_3]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_3791,plain,
% 7.49/1.50      ( k2_xboole_0(k4_xboole_0(X0,X0),X0) = k2_xboole_0(X0,X0) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_1,c_1188]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_3945,plain,
% 7.49/1.50      ( k2_xboole_0(k4_xboole_0(X0,X0),X0) = X0 ),
% 7.49/1.50      inference(light_normalisation,[status(thm)],[c_3791,c_1]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_257,plain,
% 7.49/1.50      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_5,c_0]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_3999,plain,
% 7.49/1.50      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),X1)) = k2_xboole_0(X1,X0) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_3945,c_257]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_15971,plain,
% 7.49/1.50      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0)),X2)) = k4_xboole_0(X0,k2_xboole_0(X2,k4_xboole_0(X1,X0))) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_3999,c_14184]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_16146,plain,
% 7.49/1.50      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X0))),X2)) = k4_xboole_0(X0,k2_xboole_0(X2,k4_xboole_0(X1,X0))) ),
% 7.49/1.50      inference(demodulation,[status(thm)],[c_15971,c_4]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_16147,plain,
% 7.49/1.50      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X1,X0)),X2)) = k4_xboole_0(X0,k2_xboole_0(X2,k4_xboole_0(X1,X0))) ),
% 7.49/1.50      inference(light_normalisation,[status(thm)],[c_16146,c_2476]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_16161,plain,
% 7.49/1.50      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X2,X2),X1)) ),
% 7.49/1.50      inference(demodulation,[status(thm)],[c_15963,c_16147]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_3995,plain,
% 7.49/1.50      ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_3945,c_0]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_4168,plain,
% 7.49/1.50      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),X1)) = k2_xboole_0(X0,X1) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_3995,c_5]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_15972,plain,
% 7.49/1.50      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0)),X2)) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_4168,c_14184]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_16140,plain,
% 7.49/1.50      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0)),X2)) = k4_xboole_0(X0,X2) ),
% 7.49/1.50      inference(light_normalisation,[status(thm)],[c_15972,c_14184]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_16142,plain,
% 7.49/1.50      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X0))),X2)) = k4_xboole_0(X0,X2) ),
% 7.49/1.50      inference(demodulation,[status(thm)],[c_16140,c_4]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_16143,plain,
% 7.49/1.50      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X1,X0)),X2)) = k4_xboole_0(X0,X2) ),
% 7.49/1.50      inference(light_normalisation,[status(thm)],[c_16142,c_2476]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_16162,plain,
% 7.49/1.50      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X1),X2)) = k4_xboole_0(X0,X2) ),
% 7.49/1.50      inference(demodulation,[status(thm)],[c_15963,c_16143]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_16178,plain,
% 7.49/1.50      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,X1) ),
% 7.49/1.50      inference(demodulation,[status(thm)],[c_16161,c_16162]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_9,negated_conjecture,
% 7.49/1.50      ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
% 7.49/1.50      inference(cnf_transformation,[],[f31]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_80,negated_conjecture,
% 7.49/1.50      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
% 7.49/1.50      inference(theory_normalisation,[status(thm)],[c_9,c_5,c_0]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_249,plain,
% 7.49/1.50      ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
% 7.49/1.50      inference(demodulation,[status(thm)],[c_80,c_4]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_682,plain,
% 7.49/1.50      ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
% 7.49/1.50      inference(demodulation,[status(thm)],[c_572,c_249]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_43410,plain,
% 7.49/1.50      ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
% 7.49/1.50      inference(demodulation,[status(thm)],[c_16178,c_682]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_847,plain,
% 7.49/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_734,c_5]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_854,plain,
% 7.49/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.49/1.50      inference(light_normalisation,[status(thm)],[c_847,c_5]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_27039,plain,
% 7.49/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k2_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(k2_xboole_0(X0,X1),X2)) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_1168,c_854]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_27165,plain,
% 7.49/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X2),X3)) = k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_854,c_5]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1360,plain,
% 7.49/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_1177,c_1065]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1381,plain,
% 7.49/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 7.49/1.50      inference(light_normalisation,[status(thm)],[c_1360,c_1177]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_27040,plain,
% 7.49/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(k2_xboole_0(X0,X1),X2)) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_1381,c_854]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_27043,plain,
% 7.49/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,X2)) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_838,c_854]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_258,plain,
% 7.49/1.50      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_5,c_0]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_4010,plain,
% 7.49/1.50      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X0))) = k2_xboole_0(X1,X0) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_3945,c_258]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_27064,plain,
% 7.49/1.50      ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X0)),X2)) = k2_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,X2)) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_4010,c_854]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_15964,plain,
% 7.49/1.50      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k4_xboole_0(X0,X0) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_1397,c_14184]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_391,plain,
% 7.49/1.50      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_4,c_3]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_18759,plain,
% 7.49/1.50      ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_15964,c_391]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_18772,plain,
% 7.49/1.50      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 7.49/1.50      inference(light_normalisation,[status(thm)],[c_18759,c_3995]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_19099,plain,
% 7.49/1.50      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(X0,X2) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_18772,c_5]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_21467,plain,
% 7.49/1.50      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)),X2)) = k2_xboole_0(X0,k2_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_3999,c_19099]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_21742,plain,
% 7.49/1.50      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,X1) ),
% 7.49/1.50      inference(demodulation,[status(thm)],[c_21467,c_4,c_19099]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_27074,plain,
% 7.49/1.50      ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X2)),X3)) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X3)) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_21742,c_854]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_27179,plain,
% 7.49/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_854,c_0]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_27533,plain,
% 7.49/1.50      ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,k4_xboole_0(X0,X2)),X3)) = k2_xboole_0(X0,k2_xboole_0(X3,X1)) ),
% 7.49/1.50      inference(demodulation,[status(thm)],[c_27074,c_27179]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_27552,plain,
% 7.49/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
% 7.49/1.50      inference(demodulation,[status(thm)],[c_27064,c_27533]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_27586,plain,
% 7.49/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 7.49/1.50      inference(demodulation,[status(thm)],[c_27043,c_27552]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_27589,plain,
% 7.49/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
% 7.49/1.50      inference(light_normalisation,[status(thm)],[c_27040,c_27586]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_27592,plain,
% 7.49/1.50      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X1)),X2) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 7.49/1.50      inference(demodulation,[status(thm)],[c_27039,c_27165,c_27589]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_27594,plain,
% 7.49/1.50      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X2),X1) ),
% 7.49/1.50      inference(demodulation,[status(thm)],[c_27592,c_1]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_43411,plain,
% 7.49/1.50      ( k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0))) != k2_xboole_0(sK0,sK1) ),
% 7.49/1.50      inference(demodulation,[status(thm)],[c_43410,c_2476,c_27594]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_573,plain,
% 7.49/1.50      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_3,c_5]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_585,plain,
% 7.49/1.50      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.49/1.50      inference(light_normalisation,[status(thm)],[c_573,c_5]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_3817,plain,
% 7.49/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(X0,X1)) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_1188,c_1177]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_3827,plain,
% 7.49/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_1188,c_684]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_3875,plain,
% 7.49/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 7.49/1.50      inference(light_normalisation,[status(thm)],[c_3827,c_1168]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_3889,plain,
% 7.49/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.49/1.50      inference(light_normalisation,[status(thm)],[c_3817,c_3875]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_43412,plain,
% 7.49/1.50      ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) ),
% 7.49/1.50      inference(demodulation,[status(thm)],[c_43411,c_585,c_2476,c_3889]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_43413,plain,
% 7.49/1.50      ( $false ),
% 7.49/1.50      inference(equality_resolution_simp,[status(thm)],[c_43412]) ).
% 7.49/1.50  
% 7.49/1.50  
% 7.49/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.49/1.50  
% 7.49/1.50  ------                               Statistics
% 7.49/1.50  
% 7.49/1.50  ------ General
% 7.49/1.50  
% 7.49/1.50  abstr_ref_over_cycles:                  0
% 7.49/1.50  abstr_ref_under_cycles:                 0
% 7.49/1.50  gc_basic_clause_elim:                   0
% 7.49/1.50  forced_gc_time:                         0
% 7.49/1.50  parsing_time:                           0.013
% 7.49/1.50  unif_index_cands_time:                  0.
% 7.49/1.50  unif_index_add_time:                    0.
% 7.49/1.50  orderings_time:                         0.
% 7.49/1.50  out_proof_time:                         0.01
% 7.49/1.50  total_time:                             0.961
% 7.49/1.50  num_of_symbols:                         36
% 7.49/1.50  num_of_terms:                           47711
% 7.49/1.50  
% 7.49/1.50  ------ Preprocessing
% 7.49/1.50  
% 7.49/1.50  num_of_splits:                          0
% 7.49/1.50  num_of_split_atoms:                     0
% 7.49/1.50  num_of_reused_defs:                     0
% 7.49/1.50  num_eq_ax_congr_red:                    2
% 7.49/1.50  num_of_sem_filtered_clauses:            1
% 7.49/1.50  num_of_subtypes:                        0
% 7.49/1.50  monotx_restored_types:                  0
% 7.49/1.50  sat_num_of_epr_types:                   0
% 7.49/1.50  sat_num_of_non_cyclic_types:            0
% 7.49/1.50  sat_guarded_non_collapsed_types:        0
% 7.49/1.50  num_pure_diseq_elim:                    0
% 7.49/1.50  simp_replaced_by:                       0
% 7.49/1.50  res_preprocessed:                       41
% 7.49/1.50  prep_upred:                             0
% 7.49/1.50  prep_unflattend:                        0
% 7.49/1.50  smt_new_axioms:                         0
% 7.49/1.50  pred_elim_cands:                        1
% 7.49/1.50  pred_elim:                              0
% 7.49/1.50  pred_elim_cl:                           0
% 7.49/1.50  pred_elim_cycles:                       1
% 7.49/1.50  merged_defs:                            6
% 7.49/1.50  merged_defs_ncl:                        0
% 7.49/1.50  bin_hyper_res:                          6
% 7.49/1.50  prep_cycles:                            3
% 7.49/1.50  pred_elim_time:                         0.
% 7.49/1.50  splitting_time:                         0.
% 7.49/1.50  sem_filter_time:                        0.
% 7.49/1.50  monotx_time:                            0.
% 7.49/1.50  subtype_inf_time:                       0.
% 7.49/1.50  
% 7.49/1.50  ------ Problem properties
% 7.49/1.50  
% 7.49/1.50  clauses:                                10
% 7.49/1.50  conjectures:                            1
% 7.49/1.50  epr:                                    1
% 7.49/1.50  horn:                                   10
% 7.49/1.50  ground:                                 1
% 7.49/1.50  unary:                                  7
% 7.49/1.50  binary:                                 3
% 7.49/1.50  lits:                                   13
% 7.49/1.50  lits_eq:                                8
% 7.49/1.50  fd_pure:                                0
% 7.49/1.50  fd_pseudo:                              0
% 7.49/1.50  fd_cond:                                0
% 7.49/1.50  fd_pseudo_cond:                         0
% 7.49/1.50  ac_symbols:                             1
% 7.49/1.50  
% 7.49/1.50  ------ Propositional Solver
% 7.49/1.50  
% 7.49/1.50  prop_solver_calls:                      27
% 7.49/1.50  prop_fast_solver_calls:                 310
% 7.49/1.50  smt_solver_calls:                       0
% 7.49/1.50  smt_fast_solver_calls:                  0
% 7.49/1.50  prop_num_of_clauses:                    8889
% 7.49/1.50  prop_preprocess_simplified:             14062
% 7.49/1.50  prop_fo_subsumed:                       0
% 7.49/1.50  prop_solver_time:                       0.
% 7.49/1.50  smt_solver_time:                        0.
% 7.49/1.50  smt_fast_solver_time:                   0.
% 7.49/1.50  prop_fast_solver_time:                  0.
% 7.49/1.50  prop_unsat_core_time:                   0.
% 7.49/1.50  
% 7.49/1.50  ------ QBF
% 7.49/1.50  
% 7.49/1.50  qbf_q_res:                              0
% 7.49/1.50  qbf_num_tautologies:                    0
% 7.49/1.50  qbf_prep_cycles:                        0
% 7.49/1.50  
% 7.49/1.50  ------ BMC1
% 7.49/1.50  
% 7.49/1.50  bmc1_current_bound:                     -1
% 7.49/1.50  bmc1_last_solved_bound:                 -1
% 7.49/1.50  bmc1_unsat_core_size:                   -1
% 7.49/1.50  bmc1_unsat_core_parents_size:           -1
% 7.49/1.50  bmc1_merge_next_fun:                    0
% 7.49/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.49/1.50  
% 7.49/1.50  ------ Instantiation
% 7.49/1.50  
% 7.49/1.50  inst_num_of_clauses:                    2632
% 7.49/1.50  inst_num_in_passive:                    1694
% 7.49/1.50  inst_num_in_active:                     706
% 7.49/1.50  inst_num_in_unprocessed:                233
% 7.49/1.50  inst_num_of_loops:                      720
% 7.49/1.50  inst_num_of_learning_restarts:          0
% 7.49/1.50  inst_num_moves_active_passive:          11
% 7.49/1.50  inst_lit_activity:                      0
% 7.49/1.50  inst_lit_activity_moves:                0
% 7.49/1.50  inst_num_tautologies:                   0
% 7.49/1.50  inst_num_prop_implied:                  0
% 7.49/1.50  inst_num_existing_simplified:           0
% 7.49/1.50  inst_num_eq_res_simplified:             0
% 7.49/1.50  inst_num_child_elim:                    0
% 7.49/1.50  inst_num_of_dismatching_blockings:      1593
% 7.49/1.50  inst_num_of_non_proper_insts:           2859
% 7.49/1.50  inst_num_of_duplicates:                 0
% 7.49/1.50  inst_inst_num_from_inst_to_res:         0
% 7.49/1.50  inst_dismatching_checking_time:         0.
% 7.49/1.50  
% 7.49/1.50  ------ Resolution
% 7.49/1.50  
% 7.49/1.50  res_num_of_clauses:                     0
% 7.49/1.50  res_num_in_passive:                     0
% 7.49/1.50  res_num_in_active:                      0
% 7.49/1.50  res_num_of_loops:                       44
% 7.49/1.50  res_forward_subset_subsumed:            568
% 7.49/1.50  res_backward_subset_subsumed:           2
% 7.49/1.50  res_forward_subsumed:                   0
% 7.49/1.50  res_backward_subsumed:                  0
% 7.49/1.50  res_forward_subsumption_resolution:     0
% 7.49/1.50  res_backward_subsumption_resolution:    0
% 7.49/1.50  res_clause_to_clause_subsumption:       102319
% 7.49/1.50  res_orphan_elimination:                 0
% 7.49/1.50  res_tautology_del:                      437
% 7.49/1.50  res_num_eq_res_simplified:              0
% 7.49/1.50  res_num_sel_changes:                    0
% 7.49/1.50  res_moves_from_active_to_pass:          0
% 7.49/1.50  
% 7.49/1.50  ------ Superposition
% 7.49/1.50  
% 7.49/1.50  sup_time_total:                         0.
% 7.49/1.50  sup_time_generating:                    0.
% 7.49/1.50  sup_time_sim_full:                      0.
% 7.49/1.50  sup_time_sim_immed:                     0.
% 7.49/1.50  
% 7.49/1.50  sup_num_of_clauses:                     2499
% 7.49/1.50  sup_num_in_active:                      128
% 7.49/1.50  sup_num_in_passive:                     2371
% 7.49/1.50  sup_num_of_loops:                       143
% 7.49/1.50  sup_fw_superposition:                   7432
% 7.49/1.50  sup_bw_superposition:                   6522
% 7.49/1.50  sup_immediate_simplified:               6241
% 7.49/1.50  sup_given_eliminated:                   1
% 7.49/1.50  comparisons_done:                       0
% 7.49/1.50  comparisons_avoided:                    0
% 7.49/1.50  
% 7.49/1.50  ------ Simplifications
% 7.49/1.50  
% 7.49/1.50  
% 7.49/1.50  sim_fw_subset_subsumed:                 0
% 7.49/1.50  sim_bw_subset_subsumed:                 0
% 7.49/1.50  sim_fw_subsumed:                        965
% 7.49/1.50  sim_bw_subsumed:                        28
% 7.49/1.50  sim_fw_subsumption_res:                 0
% 7.49/1.50  sim_bw_subsumption_res:                 0
% 7.49/1.50  sim_tautology_del:                      0
% 7.49/1.50  sim_eq_tautology_del:                   500
% 7.49/1.50  sim_eq_res_simp:                        0
% 7.49/1.50  sim_fw_demodulated:                     3494
% 7.49/1.50  sim_bw_demodulated:                     217
% 7.49/1.50  sim_light_normalised:                   2349
% 7.49/1.50  sim_joinable_taut:                      315
% 7.49/1.50  sim_joinable_simp:                      0
% 7.49/1.50  sim_ac_normalised:                      0
% 7.49/1.50  sim_smt_subsumption:                    0
% 7.49/1.50  
%------------------------------------------------------------------------------
